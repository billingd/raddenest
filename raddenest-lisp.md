# raddenest for maxima in lisp

## Why Lisp?

Why not just use the maxima code in raddenest.mac?

I have been unsuccessful trying to integrate maxima language code into
core maxima.  I tried with sqrtdnst.mac before writing sqrtdenest.lisp.
There were issues after kill(all), etc.

## How

I am starting with a function by function translation. Each lisp
function will be a direct replacement for the maxima function.  This
simplifies testing.  I tried other ways but couldn't find all the bugs.
Once/if it works then there are *opportunities for improvement*.

## When

Whenever.

## Progress

The following is a function in the maxima version, with those
translated to lisp ~~struck through~~.

* ~~_sqrtp~~ 
* ~~_sqrtpowerp~~
* ~~_algebraicp~~
* ~~_sqrt_depth~~
* ~~_complexity~~
* ~~_sqrtcontract~~
* ~~_sqrtcontract0~~
* ~~_ss(n)~~ not required
* ~~_subsets~~
* ~~_splitcoef~~
* ~~_sqrt_match~~
* ~~_split_gcd~~
* ~~_split_surds~~
* ~~raddenest~~
* ~~_raddenest0~~
* ~~_sqrtdenest_rec~~
* ~~_sqrtdenest1~~
* ~~_sqrt_symbolic_denest~~
* ~~_sqrt_numeric_denest~~
* ~~_sqrt_biquadratic_denest~~
* _denester
* ~~_cardano_poly~~
* ~~_rad_denest_cardano~~
* ~~_rad_denest_ramanujan~~


## How do I to use it?

Just

```
load("./raddenest.mac");
load("./raddenest.lisp");
```

then follow the instructions for the maxima version.

The results are almost identical to the maxima version.  One test in the testsuite gives a different, but apparently correct, result.
