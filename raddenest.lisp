#|
Most of the code in this Maxima package is a rather direct port of Sympy's
denesting code:
http://docs.sympy.org/1.0/_modules/sympy/simplify/sqrtdenest.html
http://docs.sympy.org/1.0/_modules/sympy/simplify/radsimp.html
The code is licensed under the GPL-compatible "3-clause BSD license".

**************************************************************************
Copyright (c) 2006-2017 SymPy Development Team (original code)
Copyright (c) 2017 Gilles Schintgen (Maxima port and extensions)
Copyright (c) 2021 David Billinghurst (Translation to maxima/lisp)

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

  a. Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimer.
  b. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  c. Neither the name of SymPy nor the names of its contributors
     may be used to endorse or promote products derived from this software
     without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
DAMAGE.
**************************************************************************

RADDENEST

This package denests different classes of expressions with nested
roots. Most of the algorithms are specific to square roots, but some
handle higher roots.

The implemented algorithms are documented in the following articles:

[1] Allan Borodin, Ronald Fagin, John E. Hopcroft, and Martin Tompa:
    "Decreasing the Nesting Depth of Expressions Involving Square Roots"
    J. Symbolic Computation (1985) 1, 169-188
    http://researcher.watson.ibm.com/researcher/files/us-fagin/symb85.pdf

[2] David J. Jeffrey and Albert D. Rich:
    "Symplifying Square Roots of Square Roots by Denesting"
    in "Computer Algebra Systems: A Practical Guide",
    M.J. Wester, Ed., Wiley 1999
    http://www.cybertester.com/data/denest.pdf

[3] Thomas J. Osler:
    "Cardan Polynomials and the Reduction of Radicals"
    Mathematics Magazine 74(1), Feb. 2001
    http://www.rowan.edu/open/depts/math/osler/mathmag026-032.pdf

[4] Mascha Honsbeek:
    "Radical Extensions and Galois Groups", Chapter 3
    (PhD Thesis)
    http://www.math.kun.nl/~bosma/students/honsbeek/M_Honsbeek_thesis.pdf

As such, the raddenest function should be able to denest some or all
of the denestable expressions of the following types:

* square roots of sums of (multiple) unnested square roots
    (_sqrtdenest_rec)

* expressions of the form sqrt(a + b*sqrt(r)) that denest using square
    roots can be denested numerically or symbolically
    (_sqrt_symbolic_denest)

* expressions of the form sqrt(a + b*sqrt(r)) where a, b, and r are
    linear combinations of square roots of positive rationals
    (_sqrt_biquadratic_denest)

* expressions of the form sqrt(a + b*sqrt(r)) that can be denested
    using fourth roots

* n-th roots of a+b*sqrt(r)
    (_rad_denest_cardano)

* square roots of a sum of two cube roots
    (_rad_denest_ramanujan)


INTERPRETATION OF RADICAL EXPRESSIONS

In general a^(1/n) has n different values.

However Maxima always simplifies such numeric expressions for positive
real 'a' and for negative real 'a' in case of a square root:
    sqrt(-4)=2*%i, 8^(1/3)=2
This is independent of the global 'domain' variable.

With domain=complex Maxima no longer simplifies a^(1/n) for negative
real 'a'. It will only factor out (-1)^(1/n) which is then treated
according to the global variable m1pbranch. It also no longer simplifies
sqrt(x^2).

Raddenest should give results that are consistent with the above.

Example:
    (2-sqrt(5))^(1/3) = 1/2-sqrt(5)/2
This denesting is only performed when domain=real and the cube root
is interpreted as a real-valued function over the reals.


IMPLEMENTATION NOTES

Functions whose names begin with an underscore are internal helper
functions. As such the only user-level function is the main command
"raddenest".

raddenest and _raddenest0 are relatively simple wrapper functions that
apply the various algorithm functions to the given expression and its
subexpressions.

POSSIBLE IMPROVEMENTS AND FURTHER READING

[5] Richard Zippel:
    "Simplification of Expressions Involving Radicals"
    J. Symbolic Computation (1985) 1, 189-210
    http://www.sciencedirect.com/science/article/pii/S0747717185800146

[6] Susan Landau:
    "Simplification of Nested Radicals"
    1993
    https://www.researchgate.net/publication/2629046_Simplification_of_Nested_Radicals

[7] Johannes Blömer:
    "Simplifying Expressions Involving Radicals"
    PhD Thesis, 1993
    http://www.cs.nyu.edu/exact/pap/rootBounds/sumOfSqrts/bloemerThesis.pdf
|#



;;; Probably want a predicate that is true when
;;; expr is not a rational, but expr^2 is a (positive?) rational
;;; 
;;; Accept sqrt(125)=5^(3/2), sqrt(1/2)=2^(-1/2)
;;;
;;; What about complex numbers?


(defmfun $_sqrtp (expr)
  "Returns true iff expr is a literal square root, i.e. radicand^(1/2)"
  (cond
   ((not (mexptp expr)) nil)
   ((alike1 (third expr) 1//2) t)
   (t nil)))


(defmfun $_sqrtpowerp (expr)
  "Returns true iff expr can be interpreted as a square root i.e. 5^(3/2)"
  ;; Maxima automatically simplifies sqrt(125) to 5^(3/2).
  ;; Negative exponents are rejected (unlike sqrtpower2p)
  (let (exponent)
    (cond
     ((not (mexptp expr)) nil)
     ((not (ratnump (setq exponent (third expr)))) nil) 
     ((not (eq ($denom exponent) 2)) nil)
     ((plusp ($num exponent)) t)  ; numerator of power > 0
     (t nil))))


(defmfun $_sqrtpower2p (expr)
  "Returns true iff expr can be interpreted as a square root.
   Unlike sqrtpower, negative exponents are accepted"
  ;;  Maxima automatically simplifies sqrt(125) to 5^(3/2).
  (let (exponent)
    (cond
     ((not (mexptp expr)) nil)
     ((not (ratnump (setq exponent (third expr)))) nil) 
     ((not (eq ($denom exponent) 2)) nil)
     (($integerp ($num exponent)) t)
     (t nil))))


(defmfun $_algebraicp (p)
  "Returns true if p is comprised only of integers, rationals or
   square(!) roots of rationals and algebraic operations."
  (cond
   (($ratnump p) t)
   (($atom p) nil)
   ;; algebraic^(-1) or algebraic^(something/2)
   ;; should the denominator be tested
   ((mexptp p)
     (and (or (eq (third p) -1) (eq ($denom (third p)) 2))
	  ($_algebraicp (second p))))
   ((or (mplusp p) (mtimesp p)) 
     (every (lambda (x) ($_algebraicp x)) (rest p))) ; is rest the best?
   (t nil)))


(defmfun $_sqrt_depth (p)
  ;;  Returns the maximum nesting depth of any square root argument of p,
  ;;    where p is an algebraic expression as defined by ?algebraicp.
  ;;
  ;;    Neither of these square roots contains any other square roots
  ;;    so the depth is 1:
  ;;    (%i1)   _sqrt_depth(1 + sqrt(2)*(1 + sqrt(3)));
  ;;    (%o1)   1
  ;;    The sqrt(3) is contained within a square root so the depth is 2:
  ;;    (%i2)   _sqrt_depth(1 + sqrt(2)*sqrt(1 + sqrt(3)));
  ;;    (%o2)   2
  (cond
    ((or ($atom p) ($ratnump p)) 0)
    ((or (mplusp p) (mtimesp p))
      (loop for x in (rest p) maximize ($_sqrt_depth x)))
    (($_sqrtpower2p p) (+ ($_sqrt_depth (second p)) 1))
    (t 0)))


(defmfun $_complexity (p)
  "Returns the Jeffrey-Rich complexity measure of expression p."
  ;;  It's similar to sqrt_depth but increases with any nesting
  ;;  of radicals (not only square roots) and penalize sums
  ;;  of radicals by adding up individual complexities.
  ;; 
  ;;  It is used as a secondary recursion termination criterion
  ;;  (after sqrt_depth) in some algorithms.
  ;;
  ;;  Reference: Jeffrey and Rich (1999), section 4.7
  ;;
  ;;  We have a radical x.  Integer N(x) is a measure of the nesting level
  ;;  (4.7.1) If x is a rational number, N(x) = 0
  ;;          For any undefined symbol,  N(x) = 0
  ;;  (4.7.2) If x=y^(m/n) is an n-th root, N(x) = N(y) + 1
  ;;  (4.7.3) If x is a product, N(xy) = max(N(x),N(y))
  ;;  (4.7.4) If x is a sum, N(a+b) = N(a) + N(b)
  (cond
    (($atom p) 0)
    (($ratnump p) 0)
    ((mplusp p) (reduce '+ (mapcar #'$_complexity (rest p))))
    ((mtimesp p) (loop for x in (rest p) maximize ($_complexity x)))
    ((and (mexptp p)
 	  ($ratnump (third p))
	  (/= ($denom (third p)) 1))
    (+ ($_complexity (second p)) 1))
    (t 0)))


;;; Contracts _all_ square roots in a given term/quotient.
;;; 
;;; Maxima's built-in commands sometimes have difficulties
;;; handling quotients with square roots in the denominator.
;;; Forcing them to contract allows for easier simplification.
;;;
;;; (%i1)   sqrt(2)/(7*sqrt(27));
;;; (%o1)   sqrt(2)/(7*3^(3/2))
;;; (%i2)   _sqrtcontract(%);
;;; (%o2)   sqrt(6)/63

(defun $_sqrtcontract (expr) (simplify (scanmap1 #'sqrtcontract0 expr)))

(defun sqrtcontract0 (prod)
  (if (mtimesp prod)   ;; prod is a product
   (let (($rootsconmode nil))
     (loop
      with rad = 1
      for term in (remove-if-not #'mexptp (rest prod))
      for r = (second term) ; term = r^e
      for e = (third term)
      do
      (if (and ($integerp r) ($ratnump e) (mminusp e) (eql ($denom e) 2))
	(setq rad (mul rad r)))
      finally
      (return(div ($rootscontract (mul* ($num prod)   (root rad 2)))
  	   ($rootscontract (mul* ($denom prod) (root rad 2)))))))
   ;; prod is not a product
   prod))


;;; (SUBSETS N)
;;;
;;; Returns all possible subsets of the set (0, 1, ..., n-1) EXCEPT THE
;;; EMPTY SET, listed in reversed lexicographical order according to binary
;;; representation, so that the case of the fourth root is treated last.
;;; Example:
;;; (%i1)   ?subsets(3);
;;; (%o2)   [[1,0,0],[0,1,0],[1,1,0],[0,0,1],[1,0,1],[0,1,1],[1,1,1]]
;;;
;;; Note: returns maxima lists.
;;;
(defmfun $_subsets (n) ($rest (subsets1 n))) ; drop first (all 0) element

;;; (SUBSETS1 N)
;;;
;;; Returns all possible subsets of the set (0, 1, ..., n-1), listed
;;; in reversed lexicographical order according to binary representation.
;;;
;;; Note: returns maxima lists.
;;
(defun subsets1 (n)
  (cond
   ((= n 1) '((mlist simp) ((mlist simp) 0) ((mlist simp) 1)))
   ((= n 2) '((mlist simp) ((mlist simp) 0 0) ((mlist simp) 1 0)
	      ((mlist simp) 0 1) ((mlist simp) 1 1)))
   ((= n 3) '((mlist simp) ((mlist simp) 0 0 0) ((mlist simp) 1 0 0)
	      ((mlist simp) 0 1 0) ((mlist simp) 1 1 0) ((mlist simp) 0 0 1)
	      ((mlist simp) 1 0 1) ((mlist simp) 0 1 1) ((mlist simp) 1 1 1)))
   (t
    (loop
     for s in (rest (subsets1 (- n 1)))
     collect `((mlist simp) 0 ,@(rest s)) into result
     collect `((mlist simp) 1 ,@(rest s)) into result
     finally (return `((mlist simp) ,@result))))))


;;; SPLITCOEF (P)
;;;
;;; Splits a given term p in two factors:
;;; a rational coefficient c and the remaining factors r.
;;; The return value is a list (c r)
;;; Note: 7^(3/2) is handled as 7*sqrt(7),
;;; contrary to maxima's default.
;;; Also: 15/sqrt(2) -> (15/2)*sqrt(2)
(defun $_splitcoef (p)
  (let (p_ (c 1) (r 1) base expt spl) ; default to c=1 and r=1
    (cond
      ;; single rational number => c=p and r=1
     (($ratnump p) (setq c p))
     ;; non-integer atom  => c=1 and r=1
     (($atom p) (setq r p))
     ;; contracts to a maxima atom: c=1 and r=p
     (($atom (setq p_ ($_sqrtcontract p))) (setq r p_))
     ;; single power that can be read as a sqrt
     ;;   e.g. 5^(13/2) -> [5^13, sqrt(5)]
     ;;        2^(-3/2) -> [1/4, sqrt(2)] */
     ((and (mexptp p_)
	   ($ratnump (setq base (second p_)))
           ($ratnump (setq expt (third  p_)))
	   (eql ($denom expt) 2))
      	(setq r (root base 2)) ; r = sqrt(base)
	(if (great expt 0) ; expt > 0
	    (setq c (pow base ($quotient ($num expt) 2)))
 	    (setq c (pow base ($quotient (sub ($num expt) 2) 2)))))
     ;; product - collect factors for c and r 
     ;; if any factor is a power -> recurse to split it
     ;; this handles e.g. 3*5^(3/2)
     ;; Note: this differs from the maxima code, which recurses
     ;; rather than loops	
     ((mtimesp p_)
      (loop
       for factor in (rest p_)
       if ($ratnump factor)
         collect factor into cfactors
       else if (mexptp factor) ; split this factor recursively
         do (setq spl ($_splitcoef factor))
         and collect (second spl) into cfactors ; FIXME spl is a maxima list
         and collect (third  spl) into rfactors ; FIXME spl is a maxima list
       else
         collect factor into rfactors
       finally ; convert lists of factors to a product FIXME? use mul* ?
       (setq c (apply #'mul cfactors))   ; c = product(cfactors)
       (setq r (apply #'mul rfactors)))) ; r = product(rfactors)
     (t ; c=1 and r=p
      (setq r p_)))
    ;; return value - FIXME: presently a maxima list
    (list '(mlist) c r)))


;;; sqrtratp (x)   equivalent to maxima ratnump(x^2)
;;; if expression x is:
;;;   maxima rational => t
;;    other (non-integer) atom => nil
;;;   product => recurse over terms with nested unchanged
;;;   sum => recurse over terms with nested t
;;;   sqrt => recurse into first arg with nested t
;;;   other => nil
;;;
;;; ?sqrtratp(sqrt(2))         => true
;;; ?sqrtratp(1+sqrt(2))       => false
;;; ?sqrtratp(sqrt(1+sqrt(2))) => false
;;; ?sqrtratp(sqrt(2)*3)       => true
;;; ?sqrtratp(15/sqrt(2))      => true
;;;
;;; FIXME: what to do about sqrt(-2)?    
;;;
(defun sqrtratp (x &optional nested)
  (cond
   (($ratnump x) t)
   (($atom x) nil)
   ((mtimesp x) ; A product. Examine terms with nested unchanged.
    (every (lambda (x) (sqrtratp x nested)) (cdr x)))
   ((mplusp x) ; A sum. Examine terms with nested t
      (every (lambda (x) (sqrtratp x t)) (cdr x)))
   (($_sqrtpower2p x) ; x = r^e with e=(n/2)
    ;; x is a sqrt.
    ;; if nested then return nil
    ;; otherwise examine first arg r with nested t
    (destructuring-bind (op r e) x (if nested nil (sqrtratp r t))))
   (t nil)))


(defun ratorsqrtp (p)
  "true if p is a rational or the sqrt of a rational"
  (if (or ($ratnump p) (sqrtratp p)) t nil))

;;; SQRT_MATCH (P)
;;; Returns [a, b, r] for _sqrt_match(a + b*sqrt(r)) where, in addition to
;;; matching, sqrt(r) also has the maximal sqrt_depth among addends of p.
;;; If p can't be matched, the return value is false.
;;;
;;; Example:
;;; (%o1)   _sqrt_match(2*sqrt(sqrt(5)+1)+sqrt(2)*sqrt(3)+sqrt(2)+1);
;;; (%o2)   [sqrt(2)*sqrt(3)+sqrt(2)+1,2,sqrt(5)+1]
(defmfun $_sqrt_match (x)
  (let ((p ($expand x)))
    (cond
      (($numberp p) `((mlist) ,p 0 0)) ; p is a maxima number
      ((mplusp p)                      ; p is a sum
        (if (every  #'ratorsqrtp (rest p))
          ;; "trivial" case. sum or terms without nested radicals
	  ($reverse ($_split_surds p))
	  ;; a sum p contains nested radicals
	  (sqrt_match2 p)))
      (t ; p is not a maxima number or a sum
       ;; splitcoef returns a maxima list [b,r] where p = b*sqrt(r)
       (destructuring-bind (op b r) ($_splitcoef p)
	  (if ($_sqrtp r) `((mlist) 0 ,b ,(pow r 2)) nil))))))


;;; comparison function for sqrt_match2
;;;
;;; Is depth of v1 > v2, lisp lists (depth expr)
(defun depth> (v1 v2)
  (cond
   ((> (first v1) (first v2)) t)
   ((< (first v1) (first v2)) nil)
   (t ($ordergreatp (second v1) (second v2)))))


;;; helper for sqrt_match
;;; p is a sum containing at least one nested radical
;;; assume that p was expanded prior to call
;;;
;;; Returns [a, b, r] for _sqrt_match(a + b*sqrt(r))
;;; If p can't be matched, the return value is false.
(defun sqrt_match2 (p)
  (if (not (mplusp p)) (merror "sqrt_match2: not a sum ~a" p))
  (let (v nmax r depth)
    ;; for each arg of p generate list (sqrt_depth(arg),arg)
    (setq v
	  (loop for x in (rest p)
		collect (list ($_sqrt_depth x) x)))
    (loop ; find nmax - the arg with maximum depth
      for term in (rest v)
      if (null nmax) do (setq nmax term)
      else if (depth> term nmax) do (setq nmax term))
    (setq depth (first nmax))
    (if (= depth 0) ; all args have sqrt_depth = 0
	(return-from sqrt_match2 nil))
    ;; find r from term with maximum depth (which is > 0)
    ;; if term is a product then set r to the factor with maximum depth
    ;; and other factors will form coefficient b
    (setq r (maximum-depth-term (second nmax) (first nmax)))
    ;; Now loop over terms in sum p collecting terms containing r
   (loop
     with b = nil
     for (d x i) in v
     if (< d depth) ; term can't contain r as d < depth
       collect x into alist
     else
       if (alike1 x r)
         collect 1 into blist
       else
	 if (mtimesp x) ; term x is a product
           if (setq b (split_product x r)) ; x = b*r
             collect b into blist
           else
	     collect x into alist
         else
           collect x into alist
     finally
       (return `((mlist) ,(apply #'add alist) ,(apply #'add blist)
		     ,(power r 2))))))  

;;; extract factor(s?) with maximum depth d from product p
;;; d is maximum sqrt depth of terms in p
;;;
;;; Does (maximum-depth-term ('$x 2) => '$x make sense?
;;;
;;; This requires further investigation.  Should this return all factors
;;; of maximum depth, or just one.  If so, which one?
;;; Look at references for clue.
(defun maximum-depth-term (p d) 
  (if (mtimesp p)
      ;; p is a product. return product of factors with depth=d
      (loop
       for x in (rest p)
       if (= ($_sqrt_depth x) d) collect x into xlist
       finally (if xlist
		 (return (apply #'mul xlist))
		 (merror "maximum-depth-term: giving up for p: ~a" p)))
      ;; p is not a product.  return p
      p))


;;; p is a product
;;; If r is a factor of p, return b where p = b*r
;;; Otherwise return nil
;;;
;;; r may be a product.  Each of the factors of r must be a factor of p.
(defun split_product (p r)
  (if (not (mtimesp p)) (merror "split_product: not a product ~a" p))
  (loop ; over rf, the factors of r
   with plist = (rest p) ; factors of p
   for rf in (if (mtimesp r) (rest r) (list r))
   ;; immediately return nil if rf not a factor of p
   always (member rf plist :test #'alike1)
   ;; remove rf from plist
   do (setq plist (remove rf plist :test #'alike1 :count 1))
   finally (return (apply #'mul plist))))

;;; SPLIT_GCD (A)    Note: lists are maxima lists
;;;
;;; Splits the list of integers a into two lists of integers, a1 and a2,
;;; such that a1 have a common divisor g=gcd(a1) and the integers in a2
;;; are not divisible by g.
;;; The result is returned as maxima list [g, a1, a2].
;;;
;;; Example:
;;;
;;; (%i1)   ?split_gcd([55, 35, 22, 14, 77, 10]);
;;; (%o2)   [5, [55, 35, 10], [22, 14, 77]]
;;;
(defmfun $_split_gcd (a)  
  (loop
   with g=nil
   for x in (rest a) ; all elements in maxima list a
   for g1 = x then ($gcd g x)
   if (= g1 1) collect x into a2
   else collect x into a1 and do (setq g g1)
   finally (return `((mlist) ,g ((mlist) ,@a1) ((mlist) ,@a2)))))


;;; split_surds (expr)
;;;
;;; Splits a sum with terms whose squares are rationals
;;; into a sum of terms a whose surds squared have gcd equal to g
;;; and a sum of terms b with surds squared prime with g.
;;;
;;; expr is a simplified sum. Consequently at least one term must be a surd.
;;; Otherwise expr would have been simplified to a rational.
;;;
;;; return maxima list [g,a,b] with expr = a*sqrt(g) + b
;;;
;;; Example:
;;;
;;; (%i1)   _split_surds(3*sqrt(3)+sqrt(5)/7+sqrt(6)+sqrt(10)+sqrt(15))
;;; (%o1)   [3, sqrt(2) + sqrt(5) + 3, sqrt(5)/7 + sqrt(10)]
;;;
(defmfun $_split_surds (expr)
  (if (not (mplusp expr)) (merror "split_surds: arg not a sum"))
  (let (args coeff_muls surds result g b1 b2)
    (setq args (rest ($rootscontract expr)))
    ;(format t "split_surds: args = ~a~%" args) ; args is lisp list
    (setq coeff_muls (mapcar #'$_splitcoef args))
    ;(format t "split_surds: coeff_muls = ~a~%" coeff_muls)
    ;; 
    (loop
     for (op c s) in coeff_muls
     ;do (format t "c: ~a s: ~a~%" c s)
     if ($_sqrtp s) collect (power s 2) into surds
     finally
       ;(format t "surds: ~a~%" surds)
       (setq result ($_split_gcd `((mlist) ,@(sort surds #'<)))))
    ;(format t "result: ~a~%" result)
    (setq g (second result))
    (setq b1 (third result))
    (setq b2 (fourth result))
    ;(format t "g: ~a~%" g)
    ;(format t "b1: ~a~%" b1)
    ;(format t "b2: ~a~%" b2)
    ;; If list b2 is empty and b1 has more than one element
    ;; then search for a larger common factor in b1
    (if (and (null (second b2)) (third b1))
	(loop
	 for x in (rest b1)
	 if (not (alike1 x g)) collect (div x g) into list
	 finally (destructuring-bind
		  (op g1 junk1 junk2)
		  ($_split_gcd `((mlist) ,@list))
		  (setq g (mul g g1)))))
    ;; split original terms into lists for a and b
    (loop
     with radicand
     for (op c s) in coeff_muls
     ;do (format t "c: ~a s: ~a~%" c s)
     if (and ($_sqrtp s) (member (setq radicand (second s)) (rest b1)))
       ;do (format t "collect into alist~%") and
       collect (mul c (root (div radicand g) 2)) into alist
     else
       ;do (format t "collect into blist~%")
       collect (mul c s) into blist
     finally
       (return `((mlist) ,g ,(apply #'add alist) ,(apply #'add blist))))))
