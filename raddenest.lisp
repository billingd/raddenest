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

A gentle introduction to the theory of denesting square roots of positive 
rationals is given in

[8] Eleftherios Gkioulekas
    On the denesting of nested square roots, 
    Int J Math Educ Sci Technol (2017), 48(6), 942–952
    DOI: 10.1080/0020739X.2017.1290831

|#

;;;Helper functions

;;; Comparison functions that use the facts database and only
;;; return t or nil.  Review usage.  Correct tests are critical
;;; The underlying comparison can return unknown.  Only accept t.

(defun my-mlessp (a b) ; a < b
  (eq (mevalp `((mlessp) ,a ,b)) t))
#|
(defun my-mleqp (a b) ; a <= b
  (eq (mevalp  `((mleqp) ,a ,b)) t))

(defun my-$equal (a b) ; a = b
  (eq (mevalp`(($equal) ,a ,b)) t))
|#
(defun my-$notequal (a b) ; a # b
  (eq (mevalp `(($notequal) ,a ,b)) t))

(defun my-mgeqp (a b) ; a >= b
  (eq (mevalp `((mgeqp) ,a ,b)) t))

(defun my-mgreaterp (a b) ; a > b
 (eq (mevalp `((mgreaterp) ,a ,b)) t))


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
	    (setq c (power base ($quotient ($num expt) 2)))
 	    (setq c (power base ($quotient (sub ($num expt) 2) 2)))))
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

(defun sqrtintegerp (x)
  ;; This gives sqrt(-2)=sqrt(2)*%i => t
  "True if x^2 is an integer"
  (cond
   (($integerp x) t)
   (($atom x) nil)
   (($ratnump x) nil)
   ;; Improve this ?
   (($integerp (power x 2)) t)
   (t nil)))

(defun sqrtposratnump (x)
  "True if x^2 is a positive rational"
  (let (x^2)
    (cond
     (($ratnump x) t)
     (($atom x) nil)
     ;; Improve this ?
     (($ratnump (setq x^2 (power x 2))) (my-mgreaterp x^2 0))
     (t nil))))
 
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Denesting functions                                                 ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; SHIM FUNCTION DURING CONVERSION

(defun _denester (nested av0 h max_depth_level)
  (simplify (mfunction-call $_denester nested av0 h max_depth_level)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; Denests sqrts in an expression that contain other square roots
;;; if possible, otherwise returns the expr unchanged.
(defmfun $raddenest (expr &optional (max_iter 3))
  (let (($algebraic t)
	($rootsconmode nil))
    (loop
     for z = ($_sqrtcontract ($_raddenest0 expr))
     repeat max_iter ; repeat must follow for (clisp complains)
     until (alike1 expr z)
     do (setq expr z)
     finally (return expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;; maxima expressions like
;;;    sqrt(sqrt(3)/2+1)/sqrt(11*sqrt(2)-12)
;;; are expressed as
;;; ((MTIMES)
;;;   ((MEXPT)
;;;     ((MPLUS) -12 ((MTIMES) 11 ((MEXPT) 2 ((RAT) 1 2))))
;;;     ((RAT) -1 2))
;;;   ((MEXPT)
;;;     ((MPLUS) 1
;;;       ((MTIMES) ((RAT) 1 2) ((MEXPT) 3 ((RAT) 1 2))))
;;;   ((RAT) 1 2)))
(defmfun $_raddenest0 (expr)
  "Returns expr after (recursively) denesting its arguments"
  (let ((ret nil)  ; return value
	($inflag t) ($algebraic t)
	ex ar val n)
    ;; The interesting case is when expr = radicand^ex
    (cond
     ;; trivial cases
     ((or ($atom expr)($ratnump expr)) (setq ret expr))
     ;; operator is "^"
     ((mexptp expr)
      (setq radicand (second expr)) ; expr = radicand^ex
      (setq ex (third expr))
      ;; Try different methods
      ;;(format t "expt branch~%  radicand ~a~%  ex ~a~%" radicand ex)
      (cond
       ;; Negative exponent. (Differs from maxima code)
       ;; Recurse with positive exponent and invert result
       ((my-mlessp ex 0)
	;;(format t "Negative exponent~%")
	(return-from $_raddenest0
		     (inv ($_raddenest0 (pow radicand (mul -1 ex))))))
	 
       ;; expr is sqrt.
       ;; Recall maxima simplifies sqrt(125) to sqrt(5)^(3/2)
       ;; expr has the form (radicand)^(n/2) for integer n
       ;; try recursive denesting using _sqrtdenest_rec
       (($_sqrtpowerp expr)
	;;(format t "raddenest0: sqrtpowerp branch~%")
	(setq radicand ($expand ($ratsimp radicand)))
	(setq ex (mul 2 ex))
	;;(format t "  radicand ~a~%  ex ~a~%" radicand ex)
	;; if radicand is a sum
	(when (mplusp radicand)
	  (setq ar (rest radicand))  ; arguments of "+"
	  ;; Three or more arguments are all square roots of integers
	  ;;(format t "In mplus clause: ar ~a~%" ar)
	  (when (and (> (length ar) 2)
		     (every #'sqrtintegerp ar))
	    ;;(format t "raddenest0: sum of three sqrts branch~%")
	    (setq val (catch 'raddenestStopIteration
			($_sqrtdenest_rec (root radicand 2))))
            (when val (return-from $_raddenest0 (pow val ex))))
	  ;; argument is sum of two cube roots of rationals
	  (when (and (eql (length ar) 2)
		     ($ratnump (pow (first ar) 3))
		     ($ratnump (pow (second ar) 3)))
	    ;;(format t "raddenest0: sum of two cube roots branch~%")
	    (setq val ($_rad_denest_ramanujan (root radicand 2)))
	    (when val (return-from $_raddenest0 (pow val ex))))
	  ;; arg is '+' but not a special case 
          ;;(format t "raddenest0: fall through branch~%")
	  (setq radicand (mapcar '$_raddenest0 ar))
	  (setq radicand ($expand (apply 'add radicand)))
	  ;;(format t "  radicand ~a ex ~a~%" radicand ex)
	  (return-from $_raddenest0
			 (pow ($_sqrtdenest1 (root radicand 2) t) ex))))
	 
	 ;; try Cardano polynomials for (a+b*sqrt(r))^(m/n)
	 ((and ;;(not (format t "Shall we try Cardan method?~%"))
	       (mexptp expr)
	       ($ratnump ex) ; exponent is rational
	       (mplusp radicand) ; radicand is a sum
	       (eql (length (setq ar (rest radicand))) 2) ; sum of two terms
	       (every #'sqrtposratnump ar))
	  ;;(format t "raddenest0: Cardan polynomials branch~%")
	  (return-from $_raddenest0 ($_rad_denest_cardano expr)))
	 
	 ;; expr is an n-th root with n even
	 (($evenp ($denom (third expr)))
	  ;;  Some fourth roots denest in two steps
	  ;;       e.g.    (19601-3465*2^(5/2))^(7/4)
	  ;;           ->  (99-35*2^(3/2))^(7/2)
	  ;;           ->  (5*sqrt(2)-7)^7
	  ;;       This is only useful if the global nesting depth
	  ;;       indeed decreases, but this is not checked by the
	  ;;       current code.
	  ;;       (Same behaviour as sqdnst.mac)
	  ;;(format t "raddenest0: n-root with n even branch~%")
	  (setq radicand ($expand ($ratsimp radicand)))
	  (setq ex (mul 2 ex)) ; 2*exponent
	  (setq val ($_raddenest0 (root radicand 2)))
	  (setq ret (pow val ex))))))

    (if ret
      ret
      (progn
	;; None of the special methods worked.  Try recursing
	;; expr must be an expression so (first expr) is the operator
	;;(format t "raddenest0: recursion branch: expr ~a~%" expr)
	;; `(,(first expr) ,@(mapcar '$_raddenest0 (rest expr))))
	(setq ret (mapcar '$_raddenest0 (rest expr)))
	($expand  `(,(first expr) ,@ret) 0 0 )))
      ))

			   

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; sqrtdenest_rec (expr)
;;; Helper that denests the square root of the sum of three or more surds.
;;;
;;; It returns the denested expression; if it cannot be denested it
;;; throws raddenestStopIteration
;;;
;;; Algorithm: expr.base is in the extension Q_m = Q(sqrt(r_1),..,sqrt(r_k));
;;; split expr.base = a + b*sqrt(r_k), where `a` and `b` are on
;;; Q_(m-1) = Q(sqrt(r_1),..,sqrt(r_(k-1))); then a^2 - b^2*r_k is
;;; on Q_(m-1); denest sqrt(a^2 - b^2*r_k) and so on.
;;;
;;; See Borodin, Fagin, Hopcroft, Tompa (1985), section 6.
;;;
;;; Examples
;;; ========
;;;
;;; (%i1)   _sqrtdenest_rec(sqrt(-72*sqrt(2) + 158*sqrt(5) + 498));
;;; (%o1)   (-sqrt(10))+9*sqrt(5)+sqrt(2)+9
;;; (%i2)   w:-6*sqrt(55)-6*sqrt(35)-2*sqrt(22)-2*sqrt(14)
;;;             +2*sqrt(77)+6*sqrt(10)+65$
;;; (%i3)   _sqrtdenest_rec(sqrt(w));
;;; (%o3)   (-sqrt(11))-sqrt(7)+3*sqrt(5)+sqrt(2)
;;;
(defmfun $_sqrtdenest_rec (expr)
  (let (($algebraic t)
	(sqrt2   `((mexpt simp) 2  ,1//2)) ; sqrt(2)
	(sqrt2/2 `((mexpt simp) 2 ,-1//2)) ; sqrt(2)/2 = 1/sqrt(2)
	r ; radicand
	g a b c ac d val)
    (block rec
      (unless (mexptp expr) (return-from rec ($raddenest expr)))
      ;; what if exponent is not 1/2, say 3/2 or -1/2
      ;; check and raise error.  Deal with it later.
      (unless ($_sqrtp expr)
	(merror "sqrtdenest_rec: arg is not a literal sqrt"))
      (setq r (second expr)) ; radicand of expr
      ;; if radicand r < 0, try denesting %i*sqrt(-r)
      (if (my-mlessp r 0) ; r (possibly symbolic) definitely < 0
	  (return-from rec (mul '$%i ($_sqrtdenest_rec (root (neg r) 2)))))
      ;; First level of denesting
      (setq val ($_split_surds r)) ; returns maxima list [g,a,b]
      (setq g (second val))
      (setq a (third val))
      (setq b (fourth val))
      (setq a (mul a (root g 2))) ; a = a*sqrt(g)
      (when (my-mlessp a b) ; if a<b, swap a and b
	(let ((tmp a)) (setq a b) (setq b tmp)))
      (setq c2 (sub (pow a 2) (pow b 2))) ; a^2-b^2
      (setq c2 ($rootscontract ($expand c2)))
      
      ;; Is there another level? expression c2 has > 2 args
      (if (and (not ($atom c2)) (> (length c2) 3))
	(let (a1 b1 c2_1 c_1 d_1 f val)
	  (setq val ($_split_surds c2)) ; returns maxima list [g,a,b]
	  (setq g (second val))
	  (setq a1 (third val))
	  (setq b1 (fourth val))
	  (setq a1 (mul a1 (root g 2))) ; a1 = a1*sqrt(g)
	  (when (my-mlessp a1 b1) ; if a1<b1, swap a1 and b1
	    (let ((tmp a1)) (setq a1 b1) (setq b1 tmp)))
	  (setq c2_1 (sub (pow a1 2) (pow b1 2))) ; a1^2-b1^2
	  (setq c2_1 ($rootscontract ($expand c2_1)))
	  
          (setq c_1 ($_sqrtdenest_rec (root c2_1 2)))
	  (setq d_1 ($_sqrtdenest_rec (root (add a1 c_1) 2)))
	  (setq f (div b1 d_1)) ; b1/d_1
          (setq f ($_sqrtcontract ($expand ($ratsimp f))))
	  ;; c = d_1*sqrt(2)/2+f*sqrt(2)/2 = (d_1+f)*sqrt(2)/2
	  (setq c (mul (add d_1 f) sqrt2/2))
          (setq c ($expand c)))
	;; else 
        (setq c ($_sqrtdenest1 (root c2 2) t)))
      ;; Time to give up?      
      (when (> ($_sqrt_depth c) 1) (throw 'raddenestStopIteration nil))
      
      (setq ac ($rootscontract (add a c)))
      ;; check for end of recursion
      ;; Is ac longer or more complex than original radicand r
      (when (and (not ($atom ac))
		 (>= (length (rest ac)) (length (rest r)))
		 (>= ($_complexity ac)
		     ($_complexity r)))
	(throw 'raddenestStopIteration nil))
      
      (setq d ($raddenest (root ac 2)))
      (when (> ($_sqrt_depth d) 1) (throw 'raddenestStopIteration nil))
      (setq r (div b d)) ; r = b/d  NOTE: r has been repurposed
      (setq r ($rootscontract ($expand ($ratsimp r))))
      (setq r (div ($expand (add (mul d sqrt2) (mul r sqrt2))) 2))
      (setq r ($rootscontract ($ratsimp r)))
      ($expand r)))) ; return r, or result from return-from above

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Return denested expr after denesting with simpler
;;; methods or, that failing, using the denester.
;;; 'denester' is a boolean indicating if _denester
;;; should be called.
(defmfun $_sqrtdenest1 (expr denester)
  (let (($inflag t)
	($algebraic t)
	a val b r d2 z dr2 dr res av0 radicand)
    (unless ($_sqrtp expr) ; not literal sqrt of form radicand^(1/2)
      (return-from $_sqrtdenest1 expr))
    (when ($atom (setq radicand (second expr)))
      (return-from $_sqrtdenest1 expr))
    (unless (setq val ($_sqrt_match radicand))
      (return-from $_sqrtdenest1 expr))
 
    ;; Trivial cases disposed of.  Now get to work.
    (setq a (second val)) ; val is a maxima list [a,b,r]
    (setq b (third val))
    (setq r (fourth val))
    ;; try a quick numeric denesting
    ;; d2 = a^2-b^2*r
    (setq d2 (sub* (pow a 2) (mul (pow b 2) r)))
    (setq d2 ($rootscontract ($expand d2)))
    (cond
     (($ratnump d2)
      (cond 			
       ((my-mgreaterp d2 0) ; d2 rational and d2 > 0
	(setq z ($_sqrt_numeric_denest a b r d2))
	(when z (return-from $_sqrtdenest1 z)))
       ;; d2 rational and d2 <= 0
       (t
        ;; fourth root case, e.g.
        ;; sqrtdenest(sqrt(3+2*sqrt(3)))
        ;;            -> sqrt(2)*3^(1/4)/2+sqrt(2)*3^(3/4)/2
        (setq dr2 ($expand (neg (mul d2 r))))
        (setq dr (root dr2 2))
        (when ($ratnump dr)
          (setq z ($_sqrt_numeric_denest ($expand (mul b r)) a r dr2))
          (when z
	    (setq z ($expand ($ratsimp (div z (root r 4)))))
	    (return-from $_sqrtdenest1 z))))))
     ;; d2 not rational
     (t
      (setq z ($_sqrt_symbolic_denest a b r))
      (when z (return-from $_sqrtdenest1 z))))

    ;; Whatever branch was selected above, it failed
    ;; Perhaps just give up
    (when (or (not denester) (not ($_algebraicp expr)))
      (return-from $_sqrtdenest1 expr))

    ;; Try _sqrt_biquadratic_denest
    (setq res ($_sqrt_biquadratic_denest expr a b r d2))
    (when res (return-from $_sqrtdenest1 res))

    ;; now try the denester
    (let (sqrt_depth_expr sqrt_depth_z expr^2_list)
      (setq sqrt_depth_expr ($_sqrt_depth expr))
      (setq av0 `((mlist) ,a ,b ,r ,d2))
      ;; maxima list [expr^2]
      (setq expr^2_list `((mlist) ,(simplify (pow expr 2))))
      (setq z (_denester expr^2_list av0 0 sqrt_depth_expr))
      (setq z (second z)) ; z[1]
      ;;denester has side-effect on av0!
      (unless (third av0) (return-from $_sqrtdenest1 expr))
      (when z
	;; Reject z if it is more complex than expr
	(if (and (= ($_sqrt_depth z) sqrt_depth_expr)
		 (>= ($_complexity z) ($_complexity expr)))
	(return-from $_sqrtdenest1 expr)
        (return-from $_sqrtdenest1 z))))

    ;; Nothing worked
    expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Given an expression, sqrt(a + b*sqrt(r)), return the denested
;;; expression or false.  This function uses the facts database
;;; for comparisons to allow denesting of symbolic expressions.
;;;
;;; Algorithm 1: standard denesting formula with d2=a^2-b^2*r
;;;              requires a>=0 and r>=0
;;; Algorithm 2: From sympy
;;;
(defmfun $_sqrt_symbolic_denest(a b r)
  (let (result)
    ;; try Algorithm 1
    (if	(setq result (sqrt_symbolic_denest_1 a b r))
      result
      ;; Didn't succeed - try algorithm 2
      (sqrt_symbolic_denest_2 a b r))))

;;; Given an expression, sqrt(a + b*sqrt(r)), return the denested
;;; expression or false.
;;;
;;; Algorithm 1:
;;; Check if the standard denesting formula with d2=a^2-b^2*r
;;; can the applied, i.e. check if d2=a^2-b^2*r is a square.
;;; For a+b*sqrt(r) = (c+d*sqrt(r))^2, a=c^2+b^2*r and
;;; a^2-b^2*r = d^4*r^2-2*c*d^2*r+c^4, quadratic in r.
;;; -> Compute the discriminant.
;;; a and r must be positive; hence denesting depends on the
;;; facts database.
;;;
;;; Examples (alg. 1):
;;; ==================
;;; (%i2) raddenest(sqrt(9*y+6*x^2*sqrt(y)+x^4));
;;; (%o2)                    sqrt(9*y + 6*x^2  sqrt(y) + x^4)
;;; (%i3) assume(y>0)$
;;; (%i4) raddenest(sqrt(9*y+6*x^2*sqrt(y)+x^4));
;;; (%o4)                           3* sqrt(y) + x^2
;;;
;;; y is a gensym with assume(y>0) in fact database.
;;;
(defun sqrt_symbolic_denest_1 (a b r)
  (let ((y ($gensym)) ; maxima gensym. assume y>0 
	(newcontext ($supcontext)) ; new context for working facts
	ca cb cc d d2 discriminant s (z nil))
    (assume `((mgreaterp) ,y 0)) ; assume(y>0)
    (when (and (my-mgeqp r 0) ;; r>=0
	       (my-mgeqp ($ratsubst y r a) 0)) ; a>=0
      ;; Is d2=a^2-b^2*r a square?  Check if discriminant = 0.
      (setq d2 ($ratsubst y r (sub (pow a 2) (mul (pow b 2) r))))
      (when (alike1 ($hipow d2 y) 2)
        (setq ca ($ratcoef d2 y 2)) ; d2 = ca*y^2 + cb*y + cc
          (when ($ratnump (root ca 2))	
	    (setq cb ($ratcoef d2 y 1))
	    (setq cc ($ratcoef d2 y 0))
	    (setq discriminant (sub (pow cb 2) (mul 4 ca cc))) ;cb^2-4*ca*cc
	    (when (alike1 discriminant 0)
	      ;; If discriminant is 0, polynomial d2 can be factored
	      ;; as a perfect square. sqrt(d2) = d = sqrt(ca)*(r+cb/(2*ca))
	      (setq d (mul (root ca 2) (add r (div cb (mul 2 ca)))))
	      ;; If b is of constant sign (>=0 or <=0), a denesting
	      ;; should not be rejected simply because b could be zero
	      ;; for isolated values of the involved variables.
	      (assume `(($notequal) ,b 0)) ; assume(notequal(b,0))
	      (setq s ($signum b)) ; only accept s = signum(b) = +/- 1
	      (when (or (equal s 1) (equal s -1))
		;; z = sqrt(a/2+d/2)+signum(b)*sqrt(a/2-d/2)
		(setq z (add (root (add (div a 2) (div d 2)) 2)
       			     (mul s (root (sub (div a 2) (div d 2)) 2))))
		(setq z ($ratsimp z)))))))
    ;; tidy up and return z (which is nil if denesting is unsuccessful)
    (killcontext newcontext)
    z))

;;; Given an expression, sqrt(a + b*sqrt(r)), return the denested
;;; expression or false.
;;;
;;; Algorithm 2 (Sympy):
;;; If r = ra + rb*sqrt(rr), try replacing sqrt(rr) in 'a' with
;;; (y^2 - ra)/rb, and if the result is a quadratic, ca*y^2 + cb*y + cc, and
;;; (cb + b)^2 - 4*ca*cc is 0, then sqrt(a + b*sqrt(r)) can be rewritten as
;;; sqrt(ca*(sqrt(r) + (cb + b)/(2*ca))^2).
;;;
;;; Examples (alg. 2):
;;; ==================
;;;
;;; (%i1)   [a,b,r]: [16-2*sqrt(29), 2, -10*sqrt(29)+55]$
;;; (%i2)   _sqrt_symbolic_denest(a, b, r);
;;; (%o2)   sqrt(-2*sqrt(29) + 11) + sqrt(5)
;;;
;;; If the expression is numeric, it will be simplified:
;;;
;;; (%i3)   w: sqrt(sqrt(sqrt(3) + 1) + 1) + 1 + sqrt(2)$
;;; (%i4)   [a,b,r]: _sqrt_match(expand(w^2))$
;;; (%i5)   _sqrt_symbolic_denest(a,b,r);
;;; (%o5)   sqrt(sqrt(sqrt(3)+1)+1)+sqrt(2)+1
;;;
;;; Otherwise, it will be simplified depending on the value of
;;; the global "domain" variable:
;;;
;;; (%i6)   w: sqrt(expand((sqrt(1-sqrt(x))-1)^2));
;;; (%o6)   sqrt(-sqrt(x)-2*sqrt(1-sqrt(x))+2)
;;; (%i7)   [a,b,r]: _sqrt_match(w^2)$
;;; (%i8)   _sqrt_symbolic_denest(a,b,r), domain:'real;
;;; (%o8)   abs(sqrt(1-sqrt(x))-1)
;;; (%i9)   _sqrt_symbolic_denest(a,b,r), domain:'complex;
;;; (%o9)   sqrt((sqrt(1-sqrt(x))-1)^2)
;;;
(defun sqrt_symbolic_denest_2 (a b r)
  (let ((rval ($_sqrt_match r)) (z nil))
    (when rval ; rval:[ra,rb,rr] (or nil) where r = sqrt(ra+rb*srqt(rr))
    (let ((ra (second rval))
	  (rb (third rval))
	  (rr (fourth rval))
	  (y ($gensym))
	  (newcontext ($supcontext)) ; new context for working facts
	  newa ca cb cc discriminant)
      (unless (alike1 rb 0)
	(assume `((mgreaterp) ,y 0)) ; assume(y>0)
	;; newa = subst((y^2-ra)/rb,sqrt(rr),a)
	(setq newa
	      ($substitute (div (sub (pow y 2) ra) rb)
			   (root rr 2)
			   a))
	(when (equal ($hipow newa y) 2) ; newa is quadratic in y
	  (setq ca ($ratcoef newa y 2))
	  (setq cb ($ratcoef newa y 1))
	  (setq cc ($ratcoef newa y 0))
	  (setq cb (add cb b)) ; cb = cb+b,
	  ;; discriminant = cb^2-4*ca*cc
	  (setq discriminant (sub (pow cb 2) (mul 4 ca cc)))
	  (setq discriminant ($expand discriminant))
	  (when (alike1 discriminant 0)
	    ;; z = sqrt(ca*(sqrt(r)+cb/(2*ca))^2)
	    (setq z (root (mul ca (pow (add (root r 2) (div cb (mul 2 ca))) 2)) 2))
	    (if ($constantp z) (setq z ($rootscontract ($expand z)))))))
      (killcontext newcontext)))
    z))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; sqrt_numeric_denest (a,b,r,d2)
;;;
;;; Denest expr = a + b*sqrt(r), where d2 = a^2 - b^2*r > 0
;;; Return false if not denested.
;;;
;;; Borodin et al (1985) Theorem 1
;;; A formula of depth 2 over a field K can be denested using a
;;; square root of r when d = sqrt(a^2 - b^2*r) is an element of K.
;;;
;;; Borodin et al (1985) Theorem 2
;;; A formula of depth 2 over a field K can be denested using a
;;; fourth root of r when sqrt(r(b^2*r-a^2)) is an element of K.
;;;
;;; Borodin et al (1985) Theorem 3
;;; Roots other than square roots and fourth roots don't help if all roots are real.
;;;
(defmfun $_sqrt_numeric_denest (a b r d2)
   (let (($algebraic t) d depthr s vad vad1)
    (setq depthr ($_sqrt_depth r))
    (setq d (root d2 2))
    (setq vad (add a d))
    ;; sqrt_depth(res) <= sqrt_depth(vad) + 1
    ;; sqrt_depth(expr) = depthr + 2
    ;; There is denesting if sqrt_depth(vad)+1 < depthr + 2
    ;; If vad^2 is a rational there is a fourth root denesting
    (if (or (< ($_sqrt_depth vad) (+ depthr 1)) ($ratnump(pow vad 2)))
	(progn
	  (setq s ($signum b))
	  (setq vad1 ($ratsimp (div 1 vad))) ; 1/vad
	  ;; (sqrt(vad/2)+signum(b)*sqrt(b^2*r*vad1/2)
          ($expand (add (root (div vad 2) 2)
			(mul s (root (mul (power b 2) r (div vad1 2)) 2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; sqrt_biquadratic_denest (expr a b r d2)
;;;
;;; denest expr = sqrt(a + b*sqrt(r))
;;; where a, b, r are linear combinations of square roots of
;;; positive rationals on the rationals (SQRR) and r > 0, b != 0,
;;; d2 = a^2 - b^2*r > 0
;;;
;;; If it cannot denest it returns false.
;;;
;;; ALGORITHM
;;; Search for a solution A of type SQRR of the biquadratic equation
;;; 4*A^4 - 4*a*A^2 + b^2*r = 0                               (1)
;;; sqd = sqrt(a^2 - b^2*r)
;;; Choosing the sqrt to be positive, the possible solutions are
;;; A = sqrt(a/2 +/- sqd/2)
;;; Since a, b, r are SQRR, then a^2 - b^2*r is a SQRR,
;;; so if sqd can be denested, it is done by
;;; _sqrtdenest_rec, and the result is a SQRR.
;;; Similarly for A.
;;;
;;; Examples of solutions (in both cases a and sqd are positive):
;;;
;;;   Example of expr with solution sqrt(a/2 + sqd/2) but not
;;;   solution sqrt(a/2 - sqd/2):
;;;   expr: sqrt(-sqrt(15) - sqrt(2)*sqrt(-sqrt(5) + 5) - sqrt(3) + 8);
;;;   a: -sqrt(15) - sqrt(3) + 8;
;;;   sqd = -2*sqrt(5) - 2 + 4*sqrt(3)
;;;
;;;   Example of expr with solution sqrt(a/2 - sqd/2) but not
;;;   solution sqrt(a/2 + sqd/2):
;;;   w: 2 + sqrt(2) + sqrt(3) + (1 + sqrt(3))*sqrt(2 + sqrt(2) + 5*sqrt(3))
;;;   expr: sqrt(expand(w^2))
;;;   a: 4*sqrt(6) + 8*sqrt(2) + 47 + 28*sqrt(3)
;;;   sqd: 29 + 20*sqrt(3)
;;;
;;; Define B = b/(2*A); eq.(1) implies a = A^2 + B^2*r; then
;;; expr^2 = a + b*sqrt(r) = (A + B*sqrt(r))^2
;;;
;;; Examples
;;; ========
;;; (%i1)   z: sqrt((2*sqrt(2) + 4)*sqrt(2 + sqrt(2)) + 5*sqrt(2) + 8)$
;;;         [a,b,r] : _sqrt_match(z^2)$
;;;         d2: a^2 - b^2*r$
;;;         _sqrt_biquadratic_denest(z, a, b, r, d2);
;;; (%o1)   sqrt(2) + sqrt(sqrt(2) + 2) + 2
;;;
(defmfun $_sqrt_biquadratic_denest (expr a b r d2)
  (let (($algebraic t)
	(z nil) ; default return value
	sqd x1 x2 A_ B_)
    (block biquad
      (unless (my-mgreaterp r 0) (return-from biquad)) ; check r>0
      (unless (my-$notequal b 0) (return-from biquad)) ;       b#0
      (unless (my-mgeqp d2 0)    (return-from biquad)) ;       d2 >= 0
      (if (< ($_sqrt_depth (second expr)) 2) (return-from biquad))
      ;; check that all terms in the linear combinations a, b, r
      ;;    have integer square
      (loop
        for x in (list a b r) do
        (loop
	  ;; If x is a sum, check each term in x. Otherwise check x.
          for y in (if (not (mplusp x)) (list x) (rest x))
          for y2 = (pow y 2)
	    if (or (not (integerp y2)) (mnegp y2))
	    do (return-from biquad)))
      (setq sqd ($raddenest (root d2 2)))
      (if (> ($_sqrt_depth sqd) 1) (return-from biquad))
      (setq x1 (add (div a 2) (div sqd 2))) ; a/2+sqd/2
      (setq x2 (sub (div a 2) (div sqd 2))) ; a/2-sqd/2
      ;; look for a solution A with depth 1
      (loop
       for x in (list x1 x2)
       for A_ = ($raddenest (root x 2))
       when (<= ($_sqrt_depth A_) 1)
       do
         (setq B_ (div b (mul 2 A_))) ; B = b/(2*A)
         (setq B_ ($ratsimp ($rootscontract ($expand ($ratsimp B_)))))
         (setq z (add A_ (mul B_ (root r 2)))) ; z = A+B*sqrt(r)
	 (if (mnegp z) (setq z (neg z)))
	 (setq z ($expand z))
	 (return-from biquad))) ; exit loop as denesting found and set to z
    z)) ; reach here via a return-from with z nil or set in last loop

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; _denester goes here

;;; product_is_square (terms factor)
;;;
;;; terms is a maxima list of rational numbers with $numberp(term)=true
;;; subset is a maxima list of 0s and 1s
;;; Is the product of terms in nested given by subset=1 a perfect square?
;;; If so, return val = sqrt(product), otherwise nil
(defun product_is_square (terms factor m)
  (let (product val)
    (loop
     for term in (rest terms) ; maxima list
     for f in (rest factor)  ; factor is a maxima list
     for i = 1 then (+ i 1)  ; to identify the m-th term
     ;; if term[m] is combined with other terms. Multiply by -1.
     if (and (= f 1) (= i m)  p) collect -1 into p
     if (= f 1) collect term into p
     finally
       (setq product (apply #'mul p)) ; product of terms with factor[i]=1
       (setq val (root product 2))  ; sqrt(product)
       (when ($ratnump val) (return val)))))

;;; find_perfect_square (nested m)
;;;
;;; nested is a (maxima) list of m radicands. Find a subset whose
;;; product is a perfect square val^2 for rational val.
;;;
;;; Borodin et al (1985) p181
;;;
;;; Find a perfect square x^2 among products of the m input radicands.
;;; Before entering the radicand of nested[m] into any product with
;;; at least one other radicand, it should be multiplied by -1. Record
;;; the radicands entering into the product by placing 1’s into the
;;; appropriate cells of the array factor. Return x.
;;; If no perfect square is found, set factor [i] = 0 for all i
;;; and return sqrt(nested[m]).
;;;
;;; Given a (maxima) list term of m rationals, find a subset whose
;;; product is a perfect square val^2 for rational val.
;;;
;;;Return maxima list [val,subset] or false/nil if no match
;;;   val - value of square root of product of selected terms
;;;   factor - maxima list of 0s and 1s denoting subset chosen
;;;
;;; Borodin (1985), Section 3 has a more sophisticated approach.
(defun find_perfect_square (nested m)
  (loop ; until a perfect square is found
    for factor in (rest ($_subsets m)) ; another maxima list
    for val = (product_is_square nested factor m)
    until val
    finally
      (unless val ; No perfect square found
	;;(format t "val: ~a~%" val)
	;;(format t "(last nested): ~a~%" (last nested))
        (setq val (root (car (last nested)) 2))
	;;(format t "val: ~a~%" val)
        (setq factor `((mlist) ,@(make-list m :initial-element 0))))
      (return `((mlist) ,val ,factor))))

;;; Can write subsets using the logbitp function
;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; rad_denest_cardano (expr)
;;;
;;; Denests expr=(a+b*sqrt(r))^(m/n) using Cardano polynomials.
;;;
;;; Reference: Osler (2001)
;;;
(defmfun $_rad_denest_cardano (expr)
  (unless (mexptp expr) (merror "rad_denest_cardano: expr not an mexpt"))
  (let (a b r m n divs sig radicand exponent result
          ($ratprint nil)
	  ($bftorat nil)
	  (prec 169) ; fpprec equivalent to $fprec=50
	  ($ratepsilon 1.0e-40))
    ;; decompose expr = radicand^exponent to (a+b*sqrt(r))^(m/n)
    (setq radicand (second expr))
    (setq exponent (third expr))
    (setq result ($_sqrt_match radicand)) ; [a,b,r]: sqrt_match(radicand)
    (if (null result)
	(merror "rad_denest_cardano: sqrt_match returned nil"))
    (setq a (second result))
    (setq b (third result))
    (setq r (fourth result))
    (setq m ($num exponent))
    (setq n ($denom exponent))
    ;; keep sign; reinterpret as a+sqrt(b) as in ref. article
    ;; Osler works denests expressions of form (a+sqrt(b))^(m/n)
    (setq sig ($signum b))
    (setq b (mul (power b 2) r))
    ;; (lisp) list of divisors of denominator n from largest to smallest
    (setq divs (reverse (rest (take '($divisors) n))))
    ;; check each divisor of the radical's index
    (loop
     with p with ps with s with x = ($gensym)
     for d in divs
     for c = (root (sub (pow a 2) b) d) ; c = (a^2-b)^(1/d)
     if ($ratnump c) do
       ;; If c is rational then expr can be denested if s is a rational root of p
       ;; where
       ;;        p(x) = cardano_poly(d,c,x)-2*a
       ;;
       ;;        s = (a+sqrt(b))^(1/d) + (a-sqrt(b))^(1/d)
       ;;
       ;; To avoid excessive numeric evaluations of the polynomial a
       ;; single rational candidate is checked. This candidate is a rational
       ;; approximation of s. The given values for fpprec
       ;; and ratepsilon are heuristic in nature.
       ;; p(x) = cardano_poly(d,c,x)-2*a
       (setq p (sub (cardano_poly d c x) (mul 2 a))) 
       ;;(setq p ($horner (mul p ($denom p))))
       ;; s = (a+sqrt(b))^(1/d)+(a-sqrt(b))^(1/d)
       (setq s (add (root (add a (root b 2)) d)   ; s = (a+sqrt(b))^(1/d)
     		    (root (sub a (root b 2)) d))) ;    +(a-sqrt(b))^(1/d)
       (setq s (different-precision-bfloat s prec))
       (setq s ($rat s)) ; rational approximation to s
       (setq ps ($expand ($ratsubst s x p)))
       (if (alike1 ps 0) 
         (progn
	   ;; result = ((s+sig*sqrt(s^2-4*c))/2)^(d/n))^m
	   (setq result
		 (power
		  (div (add s (mul sig (root (sub (pow s 2) (mul 4 c)) 2))) 2)
		  (div (mul d) n)))
	   (setq result ($expand ($ratsimp result)))
	   (setq result (pow result m))
	   (return-from $_rad_denest_cardano result)))
     finally (return expr))))


;;; cardano_poly (n c x)
;;;
;;; "Cardano" polynomials as defined in Osler (2001)
;;;
;;;   C1(c,x) = x
;;;   C2(c,x) = x^2 - 2*c
;;;   C3(c,x) = x^3 - 3*c*x
;;;     ...
;;;   Cn(c,x) = x*C[n-1](c,x) - c*C[n-2](c,x)
;;;
;;; CHECKME: maxima routine codes variable as literal x and ignores argument x
;;;          Not sure what we should be doing here.
;;;
;;; FIXME: Could use polynomial functions from rat3[a-e].lisp directly
;;;        Could return a list, array or hashmap of polynomials as
;;;        maximum value of n is known in advance.
;;;
(defun cardano_poly (n c x)
  (let (poly poly1 poly2)
    (setq poly2 ($rat x))                           ; degree n-2
    (setq poly1 ($rat (sub (pow x 2) (mul 2 c))))   ; degree n-1
    (cond
     ((= n 1) poly2)
     ((= n 2) poly1)
     (t
      (loop
       for i from 3 to n
       do
         (setq poly (sub (mul x poly1) (mul c poly2))) ; x*poly1-c*poly2
         (setq poly2 poly1)
	 (setq poly1 poly)
       finally (return poly))))))


;;; Evaluate bfloat(expr) with maxima::fpprec=prec
;;; prec sets lisp variable maxima::fpprec ~ maxima $fpprec/log10(2)
(defun different-precision-bfloat (expr prec)
  (let (bfexpr (saved-fpprec fpprec))
    (setq fpprec prec)
    (setq bfexpr ($bfloat expr))
    (setq fpprec saved-fpprec)
    bfexpr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; rad_denest_ramanujan (expr)
;;;
;;; Denest expr=sqrt(alpha^(1/3)+beta^(1/3)) using the results
;;; of Honsbeek (2005) [4], Chapter 3.
;;; If expr can't be denested, return false.
;;;
;;; alpha and beta must be rationals; parameter checking must
;;; be done by the calling function.
;;;
(defmfun $_rad_denest_ramanujan (expr)
  (let (alpha beta c Fba (x ($gensym)) s tt res)
    (setq res (match-sqrt-of-cbrts expr)) ; maxima list [alpha,beta]
    (setq alpha (second res))
    (setq beta (third res))
    (cond
    ;;  If domain=complex, Maxima interprets a^(1/3) with a>0
    ;;  as the real branch of the cube root, but leaves the
    ;;  expression untouched if a<0.
    ((and (eql $domain '$complex)
	  (or (mnegp alpha) (mnegp beta))) nil)
    ;;  The perfect cube case can be trivially denested
    ;;  but this code segment should, in fact, not be reached
    ;;  since the simplifier already handles this case.
    (($ratnump (setq c (root ( div beta alpha) 3)));c=(beta/alpha)^(1/3)
     ;; sqrt(alpha^(1/3)*sqrt(1+c))
     (root (mul (root alpha 3) (root (add 1 c) 2)) 2)) 
    (t
     ;; Fba: t^4+4*t^3+8*beta/alpha*t-4*beta/alpha
     ;; FIXME: Fba is a polynomial with integer coeffs.
     ;;        Could use specialized routines from rat3{a-e}.lisp.
     (setq Fba (add (pow x 4) (mul 4 (pow x 3))
		    (mul 8 (div beta alpha) x) (mul -4 (div beta alpha))))
     (setq Fba ($multthru ($denom (mul 4 (div beta alpha))) Fba))
     ;; apply the rational root theorem to the polynomial Fba
     ;; to find s - any rational root (or nil on failure)
     (setq s (one-rational-root-poly Fba x 4))
     (when s
       (setq tt (sub beta (mul (pow s 3) alpha))) ;tt=beta-s^3*alpha
       ;;  Sign: either alpha^(1/3)+beta^(1/3) is positive, then
       ;;  so is its sqrt, or alpha^(1/3)+beta^(1/3) is negative,
       ;;  then its sqrt is %i times a positive real.
       ;;  Both cases are treated correctly by the formula below.
       ;;
       ;; res: sqrt(1/tt)*abs(-1/2*s^2*(alpha^2)^(1/3)
       ;;         +s*(alpha*beta)^(1/3)+(beta^2)^(1/3))
       (setq res (mul*
		  (root (inv tt) 2)
		  ($abs
		   (add
		    (mul -1//2 (pow s 2) (root (pow alpha 2) 3))
		    (mul s (root (mul alpha beta) 3))
		    (root (pow beta 2) 3)))))
       ($ratsimp res))))))

;;; Use the rational root theorem to return a rational root of
;;; an nth degree polynomial with integer coefficients.
;;; Return nil if no rational root exists.
;;;
;;;  p(x) is a maxima expression = ak*x^k + ... + a2*x^2 + a1*x + a0
;;;
;;; Each rational solution x = n/m with n and m relatively prime satisfies
;;; - n is an integer factor of a0
;;; - m is an integer factor of ak
;;;
(defun one-rational-root-poly (p x k)
  (let (div0 divk i m n (possible-roots nil))
    (setq div0 (rest (take '($divisors) ($coeff p x 0))))
    (setq divk (rest (take '($divisors) ($coeff p x k))))
    (dolist (n div0)   ; divisors of coefficient a0
      (dolist (m divk) ; divisors of coefficient ak
	(progn
          (push (div n m)       possible-roots)    ;  n/m
          (push (div (neg n) m) possible-roots)))) ; -n/m
    (setq possible-roots (delete-duplicates possible-roots :test #'alike1))
    (dolist (i possible-roots)
      ;; return first i where i is a root of p(x), otherwise nil
      (when (alike1 (maxima-substitute i x p) 0) (return i)))))
 
;;; expr=sqrt(alpha^(1/3)+beta^(1/3)) with alpha and beta rational
;;;
;;; Return maxima list [alpha,beta], or raise maxima error on failure.
;;;
;;; Just a hack for now.  May not match more complicated forms.
(defun match-sqrt-of-cbrts (expr)
  (let ((alpha nil) (beta nil) arg)
    (cond
     ((not ($_sqrtp expr)) nil) ; expr must be sqrt - test may be to strict
     ((not (mplusp (setq arg (second expr)))) nil) ;
     ((fourth arg) nil) ; only two terms allowed in arg
     (t ; have a sum of terms in cbrt.
      (setq alpha (arg-of-cbrt (second arg)))
      (setq beta  (arg-of-cbrt (third arg)))))
    (unless (and alpha beta)
      (merror "match-sum-of-cbrts: match failure"))
    `((mlist) ,alpha ,beta))) ;; maxima list [alpha,beta]

;;; ex is a maxima expression
;;; Return the rational argument of a cube-root function, or nil on failure
;;; Need to deal with expressions like (-4)^(1/3)
;;; which can be simplfied to (when domain:real) 
;;;    ((MTIMES SIMP) -1 ((MEXPT SIMP) 4 ((RAT SIMP) 1 3)))
;;; Start with the simple form similar to maxima code.
;;; Need to be careful with complex and negative args if modified.
(defun arg-of-cbrt (ex)
  (let ((r (pow ex 3)))
    (if ($ratnump r) r nil)))

