# raddenest for maxima in lisp

## Why Lisp?

Why not just use the maxima code in raddenest.mac?

I have been unsuccessful trying to integrate maxima language code into
core maxima.  I tried with sqrtdnst.mac before writing sqrtdenest.lisp.
There were issues after kill(all), etc.

## How

I am starting with a function by function translation.. Each lisp
function will be a direct replacement for the maxima function.  This
simplifies testing.  I tried other ways but couldn't get find all the bugs.
Once/if it works then there are *opportunities for improvement*.

## When

Whenever.

## How di I to use it?

Just

```
load("./raddenest.mac");
load("./raddenest.lisp");
```

then follow the instructions for the maxima version.

The results are almost identical to the maxima version.  One test in the testsuite gives a different, but apparently correct, result.
