/*
 * Copyright (c) 2026 Anders Magnusson.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *      
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <stdlib.h>
#include "config.h"
#include "cpp.h"

struct rdline *
templine(struct rdline *rdp)
{

#ifdef HAVE_FGETLN
	if ((rdp->line = fgetln(rdp->fp, (size_t *)&rdp->len)) == NULL)
		return NULL;	/* end-of-file */
#else
	if ((rdp->len = getline(&rdp->line, &rdp->alen, rdp->fp)) == -1)
		return NULL;
#endif
	if (rdp->line[rdp->len-1] != '\n')
		warning("line do not end with newline");
	rdp->curpos = rdp->line;
	return rdp;
}

struct rdline *
tempfile(FILE *fp)
{
	struct rdline *rdp = xmalloc(sizeof(struct rdline));

	if ((rdp->fp = fp) == NULL) {
		if ((rdp->fp = tmpfile()) < 0)
			error("open tempfile");
	}
	rdp->line = rdp->curpos = NULL;
	rdp->alen = rdp->len = 0;
	return rdp;
}

void
tempclose(struct rdline *rdp)
{
#ifndef HAVE_FGETLN
	free(rdp->line);
#endif
	fclose(rdp->fp);
	free(rdp);
}
