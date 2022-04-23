# run maxima raddenest tests

all: check

check: check_mac check_lisp

# Run the maxima version
check_mac: check_mac.in raddenest.mac rtest_raddenest.mac
	maxima < $<

# Run the lisp/maxima version
check_lisp: check_lisp.in raddenest.mac raddenest.lisp rtest_raddenest.mac
	maxima < $<

clean:
	-rm *~
