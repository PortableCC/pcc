# Licensing

This repository is a mixed-license source tree, but the licenses are
generally of the permissive BSD and ISC styles.

The individual file headers are authoritative; this file summarizes
the main notices found in the checked-in files and collects the
principal license texts for redistribution.

At the time this file was added, an audit of the tracked files found
the following notice families.  Counts are not mutually exclusive
where a file carries multiple notices.

- 46 files with the Caldera advertising-clause BSD-style license.
- 84 files with BSD-3-clause-style terms.
- 62 files with BSD-2-clause-style terms.
- 19 files with ISC-style "permission to use, copy, modify" terms.
- `config.guess` and `config.sub` under GPLv3-or-later with the
  Autoconf special exception.
- `configure` with the GNU Autoconf generated-script
  unlimited-permission notice.
- `install-sh` under the X Consortium/MIT-style notice, with FSF
  changes in the public domain.
- `common/strtodg.c` under the Lucent Technologies permissive notice.
- `os/midnightbsd/ccconfig.h` and `os/mirbsd/ccconfig.h` under
  permissive MirOS/MidnightBSD-style terms.
- `common/compat.h` marked public domain.
- Several generated, build, documentation, test, or configuration
  files with no standalone copyright notice visible in the file.

## Caldera BSD-Style License With Advertising Clause

This license appears on Caldera-derived files, including files in
`mip`, `f77`, `arch/vax`, and parts of `cc`.

```text
Copyright(C) Caldera International Inc. 2001-2002. All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

Redistributions of source code and documentation must retain the above
copyright notice, this list of conditions and the following disclaimer.
Redistributions in binary form must reproduce the above copyright
notice, this list of conditionsand the following disclaimer in the
documentation and/or other materials provided with the distribution.
All advertising materials mentioning features or use of this software
must display the following acknowledgement:
	This product includes software developed or owned by Caldera
	International, Inc.
Neither the name of Caldera International, Inc. nor the names of other
contributors may be used to endorse or promote products derived from
this software without specific prior written permission.

USE OF THE SOFTWARE PROVIDED FOR UNDER THIS LICENSE BY CALDERA
INTERNATIONAL, INC. AND CONTRIBUTORS ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED.  IN NO EVENT SHALL CALDERA INTERNATIONAL, INC. BE LIABLE
FOR ANY DIRECT, INDIRECT INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OFLIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
POSSIBILITY OF SUCH DAMAGE.
```

## BSD-3-Clause-Style License

Many files by Anders Magnusson and other contributors use this form,
with the copyright holder named in the individual file.

```text
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of the author may not be used to endorse or promote products
   derived from this software without specific prior written permission

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```

Some BSD-3-clause files use equivalent non-endorsement wording for a
named institution, such as the Regents of the University of California.

## BSD-2-Clause-Style License

Several newer files, including the driver and some target/common
support, use this two-clause form.

```text
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in
   the documentation and/or other materials provided with the
   distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
SUCH DAMAGE.
```

## ISC-Style License

Several manpages and target back-end files use this form, with the
copyright holder named in the individual file.

```text
Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR AND CONTRIBUTORS DISCLAIM
ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL AUTHOR AND
CONTRIBUTORS BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL
DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS
ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF
THIS SOFTWARE.
```

Some ISC-style files use "and distribute" rather than "and/or
distribute", or say "THE AUTHOR DISCLAIMS" rather than "THE AUTHOR AND
CONTRIBUTORS DISCLAIM".  Preserve each file's exact wording when
redistributing that file.

## GNU Autoconf Helper Files

`config.guess` and `config.sub` are GPLv3-or-later with the Autoconf
special exception:

```text
This file is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

As a special exception to the GNU General Public License, if you
distribute this file as part of a program that contains a
configuration script generated by Autoconf, you may include it under
the same distribution terms that you use for the rest of that
program.  This Exception is an additional permission under section 7
of the GNU General Public License, version 3 ("GPLv3").
```

`configure` is generated by GNU Autoconf and carries this notice:

```text
This configure script is free software; the Free Software Foundation
gives unlimited permission to copy, distribute and modify it.
```

## X Consortium / MIT-Style install-sh Notice

`install-sh` carries the following X Consortium notice; FSF changes to
that file are marked public domain in the file.

```text
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
X CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNEC-
TION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Except as contained in this notice, the name of the X Consortium shall not
be used in advertising or otherwise to promote the sale, use or other deal-
ings in this Software without prior written authorization from the X Consor-
tium.
```

## Lucent strtodg Notice

`common/strtodg.c` is derived from David M. Gay's gdtoa package and
carries the following Lucent notice:

```text
The author of this software is David M. Gay.

Copyright (C) 1998-2000 by Lucent Technologies
All Rights Reserved

Permission to use, copy, modify, and distribute this software and
its documentation for any purpose and without fee is hereby
granted, provided that the above copyright notice appear in all
copies and that both that the copyright notice and this
permission notice and warranty disclaimer appear in supporting
documentation, and that the name of Lucent or any of its entities
not be used in advertising or publicity pertaining to
distribution of the software without specific, written prior
permission.

LUCENT DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS SOFTWARE,
INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS.
IN NO EVENT SHALL LUCENT OR ANY OF ITS ENTITIES BE LIABLE FOR ANY
SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER
IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION,
ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF
THIS SOFTWARE.
```

## MirOS / MidnightBSD-Style Notice

`os/mirbsd/ccconfig.h` and `os/midnightbsd/ccconfig.h` carry this
permissive notice:

```text
Provided that these terms and disclaimer and all copyright notices
are retained or reproduced in an accompanying document, permission
is granted to deal in this work without restriction, including un-
limited rights to use, publicly perform, distribute, sell, modify,
merge, give away, or sublicence.

This work is provided "AS IS" and WITHOUT WARRANTY of any kind, to
the utmost extent permitted by applicable law, neither express nor
implied; without malicious intent or gross negligence. In no event
may a licensor, author or contributor be held liable for indirect,
direct, other damage, loss, or other issues arising in any way out
of dealing in the work, even if advised of the possibility of such
damage or existence of a defect, except proven that it results out
of said person's immediate fault when using the work as intended.
```

## Public Domain Notice

`common/compat.h` says:

```text
Public domain.
```
