# Copyright (C) 2022 Wing Hei Chan

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved.  This file is offered as-is,
# without any warranty.

.POSIX:
SHELL = /bin/sh
EMACS = emacs --batch --quick --directory=.
MAKEINFO = makeinfo
EL = for.el for-iteration.el for-sequence.el
ELC = $(EL:.el=.elc)
TEXI = for.texi
INFO = $(TEXI:.texi=.info)
INFOD = dir
CSS = css.html
CSS_OPT = --set-customization-variable CSS_LINES="$$(tail -n4 $(CSS))"
HTML = docs

.SUFFIXES:
.SUFFIXES: .el .elc .texi .info
.el.elc:
	$(EMACS) --funcall=batch-byte-compile $<
.texi.info:
	$(MAKEINFO) --no-split $< --output=$@

all: compile info

compile: $(ELC)

info: $(INFO)
	install-info $(INFO) $(INFOD)
html: $(CSS)
	$(MAKEINFO) --html $(CSS_OPT) $(TEXI) --output=$(HTML)

clean:
	rm -rf $(ELC) $(INFO) $(INFOD) $(HTML)
