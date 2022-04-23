

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
   ((sqrtpower2p x) ; x = r^e with e=(n/2)
    ;; x is a sqrt.
    ;; if nested then return nil
    ;; otherwise examine first arg r with nested t
    (destructuring-bind (op r e) x (if nested nil (sqrtratp r t))))
   (t nil)))
