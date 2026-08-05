/*
 * e73.c - djnz loop-counter fusion + non-loop RMW compare elision.
 *
 * Two related optimizations exercised here:
 *
 *  (A) cbfuse (arch/z8001/local2.c) turns a fused countdown loop branch
 *      "dec r,$1 ; jr ne,L" into a single "djnz r,L" (backward only; the
 *      Coherent as relaxes an out-of-range djnz to "dec;jp nz").
 *
 *  (B) rmwrenamesd (arch/z8001/local2.c) recovers the read-modify-write
 *      shape for a straight-line "if ((x op= y))" so the compare-vs-zero
 *      is elided: "sub r,rY ; jr ne" instead of "sub;test;jr".
 *
 * The oki() checks verify SEMANTICS.  To confirm the optimizations FIRED,
 * inspect the generated e73.s:
 *   - dj_while/dj_do/dj_expr  -> contain "djnz"  and NO "jr ne" loop close
 *   - rmw_sub/rmw_and/rmw_or  -> "sub/and/or ...; jr ne/eq" and NO "test"
 *   - ctl_byte  -> "dbjnz" is NOT emitted (byte counter kept as decb;jr)
 *   - ctl_step2 -> NO djnz (decrement by 2)
 *   - ctl_live  -> keeps a separate test (source stays live)
 *
 * Build (cross):
 *   ./cc/cpp/z8001-coherent-cpp.exe ztests/e73.c > f.i
 *   ./cc/ccom/z8001-coherent-ccom.exe -xtemps -xdeljumps -xssa < f.i | tr -d '\r' > e73.s
 * On Coherent:
 *   /bin/as -g -o e73.o e73.s
 *   /bin/ld -o e73 /lib/crts0.o e73.o -lc
 *   ./e73
 */

int nfail = 0;

void
oki(char *name, int got, int want)
{
	if (got == want)
		printf("ok   %s\n", name);
	else {
		printf("FAIL %s: got %d want %d\n", name, got, want);
		nfail++;
	}
}

/* ---- (A) djnz countdown loops ----------------------------------------- */

/* while (--n): decrement THEN test; classic djnz shape */
int
dj_while(int n)
{
	int c = 0;
	while (--n)
		c++;
	return c;
}

/* do { } while (--n): body runs first, backward branch on nonzero */
int
dj_do(int n)
{
	int c = 0;
	do {
		c++;
	} while (--n);
	return c;
}

/* count-down accumulator with a live-across-loop value (dj still applies) */
int
dj_expr(int n)
{
	int sum = 0;
	int k = n;
	while (--k)
		sum += k;
	return sum;
}

/* ---- (B) non-loop read-modify-write compare elision -------------------- */

int
rmw_sub(int x, int y)
{
	if ((x -= y))
		return 100 + x;
	return x;			/* x == 0 here */
}

int
rmw_and(int x, int mask)
{
	if ((x &= mask))
		return 200 + x;
	return 999;
}

int
rmw_or(int x, int bits)
{
	if ((x |= bits) == 0)
		return -1;
	return x;
}

/* ---- controls that must NOT transform --------------------------------- */

/* byte counter: dbjnz not handled -> stays decb;jr (semantics still ok) */
int
ctl_byte(int n)
{
	unsigned char b = (unsigned char)n;
	int c = 0;
	while (--b)
		c++;
	return c;
}

/* decrement by 2: not expressible as djnz */
int
ctl_step2(int n)
{
	int c = 0;
	while ((n -= 2) > 0)
		c++;
	return c;
}

/* source stays live after the RMW: rename must be rejected */
int
ctl_live(int x, int y)
{
	int r = 0;
	int t = x - y;
	if (t)
		r = 1;
	return r + (x - y);		/* recomputes x-y: x,y still live */
}

int
main()
{
	oki("dj_while.5", dj_while(5), 4);
	oki("dj_while.1", dj_while(1), 0);
	oki("dj_do.5", dj_do(5), 5);
	oki("dj_do.1", dj_do(1), 1);
	oki("dj_expr.5", dj_expr(5), 4 + 3 + 2 + 1);

	oki("rmw_sub.ne", rmw_sub(7, 3), 104);
	oki("rmw_sub.eq", rmw_sub(4, 4), 0);
	oki("rmw_and.ne", rmw_and(0xF3, 0x0F), 200 + 3);
	oki("rmw_and.eq", rmw_and(0xF0, 0x0F), 999);
	oki("rmw_or.ne", rmw_or(0, 6), 6);

	oki("ctl_byte.5", ctl_byte(5), 4);
	oki("ctl_step2", ctl_step2(6), 2);	/* 6->4(c1)->2(c2)->0 stop : 2 */
	oki("ctl_live", ctl_live(9, 4), 1 + 5);

	if (nfail == 0)
		printf("DJNZ OK\n");
	return nfail;
}
