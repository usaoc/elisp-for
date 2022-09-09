# Copyright (C) 2022 Wing Hei Chan

# Copying and distribution of this file, with or without modification,
# are permitted in any medium without royalty provided the copyright
# notice and this notice are preserved.  This file is offered as-is,
# without any warranty.

.POSIX:
SHELL = /bin/sh
EMACS = emacs --batch --quick --directory=.
MAKEINFO = makeinfo
EL = for-helper.el for-iteration.el for-sequence.el for.el
ELC = $(EL:.el=.elc)
TEST = for-tests.el
TESTC = $(TEST:.el=.elc)
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

all: compile info check

compile: $(ELC)

info: $(INFO)
	install-info $(INFO) $(INFOD)
html: $(CSS)
	$(MAKEINFO) --html $(CSS_OPT) $(TEXI) --output=$(HTML)

check: compile $(TESTC)
	$(EMACS) --load=$(TEST:.el=) --funcall=ert-run-tests-batch-and-exit

clean:
	rm -rf $(ELC) $(TESTC) $(INFO) $(INFOD) $(HTML)
