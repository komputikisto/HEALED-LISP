(load "~/quicklisp/setup.lisp")

(ql:quickload "optima")
(ql:quickload "cl-ansi-text")
(ql:quickload "alexandria")


(use-package :optima)
(use-package :cl-ansi-text)

(defparameter *trace-time-flag* t)
(setq trace-flag 'on)

(defun signed-numeric-string-p (str)
    (cond ((string= str "") nil)
          ((or (string= (subseq str 0 1) "+")
               (string= (subseq str 0 1) "-"))
           (numeric-string-p (subseq str 1)))
          ((find (elt str 0) "0123456789")
            (numeric-string-p str))))

(defun numeric-string-p (str)
    (and (>= (length str) 1)
         (map-and (lambda (i) (find i "0123456789"))
                  (coerce str 'list))))

(defun delimiter-p (chr)
      (or (char= #\( chr) (char= #\) chr)
          (char= #\Space chr) (char= #\' chr) (char= #\` chr) (char= #\, chr)
          (char= #\" chr)
          (char= #\Newline chr)
          (char= #\; chr)))

(defun read-atom (str)
      (cond ((string= str "") "")
            ((delimiter-p (elt str 0)) "")
            (t (concatenate 'string (subseq str 0 1) (read-atom (subseq str 1))))))

(defun after-atom (str)
      (cond ((string= str "") "")
            ((delimiter-p (elt str 0)) str)
            (t (after-atom (subseq str 1)))))

(defun up-to-newline (str)
    (cond ((string= str "") "")
          ((equal (elt str 0) #\Newline) (subseq str 1))
          (t (up-to-newline (subseq str 1)))))

(defun read-string (str acc success failure)
   (cond ((string= str "") (funcall failure "Unbalanced double quote"))
         ((char= #\" (elt str 0)) (funcall success acc (subseq str 1)))
         (t (read-string (subseq str 1)
                         (concatenate 'string acc (subseq str 0 1))
                         success failure))))


(defun prefix-p (str1 str2)
   (cond ((string= str1 "") t)
         ((string= str2 "") nil)
         ((char= (elt str1 0) (elt str2 0)) (prefix-p (subseq str1 1) (subseq str2 1)))
         (t nil)))

(defun read-sexpr (str success failure)
   (cond ((string= str "") (funcall failure "Expression missing"))
         ((char= #\Space (elt str 0)) (read-sexpr (subseq str 1) success failure))
         ((char= #\Newline (elt str 0)) (read-sexpr (subseq str 1) success failure))
         ((char= #\) (elt str 0)) (funcall failure "Unbalanced right parenthesis"))
         ((char= #\( (elt str 0))
            (read-tail (subseq str 1)
                       nil
                       success
                       failure))
         ((char= #\' (elt str 0)) (read-sexpr (subseq str 1)
                                              (lambda (res rest)
                                                  (funcall success (list 'quote res) rest))
                                               failure))
         ((char= #\` (elt str 0)) (read-sexpr (subseq str 1)
                                              (lambda (res rest)
                                                  (funcall success (list 'quasiquote res) rest))
                                               failure))
         ((prefix-p ",@" str) (read-sexpr (subseq str 2)
                                              (lambda (res rest)
                                                  (funcall success (list 'unquote-splicing res) rest))
                                              failure))
         ((char= #\, (elt str 0)) (read-sexpr (subseq str 1)
                                              (lambda (res rest)
                                                  (funcall success (list 'unquote res) rest))
                                              failure))
         ((char= #\; (elt str 0))
                (read-sexpr (up-to-newline str) success failure))
         ((char= #\" (elt str 0)) (read-string (subseq str 1) "" success failure))
         (t (let ((atm (read-atom str)))
                 (if (signed-numeric-string-p atm)
                     (funcall success (parse-integer atm) (after-atom str))
                     (funcall success (nil-patch atm) (after-atom str)))))))

(defparameter nil-atom (gensym))

(defun nil-patch (atm)
   (let ((upcase-atm (string-upcase atm)))
        (if (string= upcase-atm "NIL")
            nil-atom
            (intern upcase-atm))))

(defun read-tail (str acc success failure)
   (cond ((string= str "") (funcall failure "Unbalanced left parenthesis"))
         ((char= #\) (elt str 0)) (funcall success (reverse acc) (subseq str 1)))
         ((char= #\Space (elt str 0)) (read-tail (subseq str 1) acc success failure))
         (t (read-sexpr str
                        (lambda (res rest)
                            (read-tail rest (cons res acc) success failure))
                        failure))))

(defun read-bare-list (str acc success failure)
    (cond ((string= str "") (funcall success (reverse acc) ""))
          ((char= #\Space (elt str 0)) (read-bare-list (subseq str 1) acc success failure))
          ((char= #\Newline (elt str 0)) (read-bare-list (subseq str 1) acc success failure))
          ((char= #\; (elt str 0))
           (read-bare-list (up-to-newline str) acc success failure))
         (t (read-sexpr str
                        (lambda (res rest)
                            (read-bare-list rest (cons res acc) success failure))
                        failure))))

(defun verify-end-of-expr (str)
    (cond ((string= str "") t)
          ((char= #\Space (elt str 0)) (verify-end-of-expr (subseq str 1)))
          ((char= #\Newline (elt str 0)) (verify-end-of-expr (subseq str 1)))
          ((char= #\; (elt str 0))
                 (verify-end-of-expr (up-to-newline str)))
          (t nil)))

(defparameter *glob-env* nil)

(defun map-and (fn lst)
   (cond ((null lst) t)
         ((not (funcall fn (car lst))) nil)
         (t (map-and fn (cdr lst)))))

(defun map-or (fn lst)
   (cond ((null lst) nil)
         ((funcall fn (car lst)) t)
         (t (map-or fn (cdr lst)))))


(defun lambda-list-p (lst)
    (and (listp lst) (map-and (lambda (i) (symbolp i)) lst)))

(defun built-in-or-user-function-p (symb)
     (or (gethash symb builtins)
         (assoc symb *glob-env*)))

; quasiquote is in normal form if it does not contain unquote on a function
(defun quasiquote-normal-form-p (tree)
     (match tree
            ((guard x (atom x)) t)
            ((list 'unquote (list 'lambda args body)) t)
            ((guard (list 'unquote x) (built-in-or-user-function-p x)) t)
            ((guard (list 'unquote (list '/ arg1 arg2))
                    (and (numberp arg1) (numberp arg2)))
               (= 1 (gcd arg1 arg2)))
            ((list 'unquote x) nil)
            ((list 'unquote-splicing x) nil)
            (otherwise (map-and #'quasiquote-normal-form-p tree))))


(defun normal-form-p (form)
        (match form
               ((guard x (or (numberp x) (stringp x))) t)
               ((guard x (built-in-or-user-function-p x)) t)
               ((guard (list 'quote x) (not (is-quote-unnecessary x))) t)
               ('true t)
               ('false t)
               ((guard (list 'lambda formals body)
                       (lambda-list-p formals))
                  t)
               ((guard (list 'quasiquote x) (not (contains-unquote x))) nil)
               ((guard (list 'quasiquote x) (quasiquote-normal-form-p x)) t)
               ((list '/ arg1 1) nil)
               ((list '/ arg1 0) nil)
               ((guard (list '/ arg1 arg2)
                       (and (numberp arg1) (numberp arg2)
                            (= 1 (gcd arg1 arg2))
                            (> arg2 0)))
                      t)
              (otherwise nil)))

(defun data-p (form)
        (match form
               ((guard x (or (numberp x) (stringp x))) t)
               ((list 'quote x) t)
               ('true t)
               ('false t)
               (otherwise nil)))

(defun is-quote-unnecessary (a)
   (or (numberp a) (stringp a) (eq a 'true) (eq a 'false)))

(defun drop-quote-if-needed (a)
   (match a
          ((list 'quote x) x)
          ((guard x (is-quote-unnecessary x)) x)))

(defun add-quote-if-needed (a)
    (if (is-quote-unnecessary a)
        a
        (list 'quote a)))

(defun let-star-free (clauses body)
      (if (null clauses)
          (free body)
          (union (free (cadar clauses))
                 (set-difference (let-star-free (cdr clauses) body)
                                 (list (caar clauses))))))

(defun free (form)
   (match form
         ((guard x (symbolp x)) (list x))
         ((list 'lambda formals body)
           (set-difference (free body) formals))
         ((list 'let clauses body)
           (union (reduce #'union (mapcar (lambda (i) (free (second i))) clauses))
                  (set-difference (free body) (mapcar #'car clauses))))
         ((list 'let* clauses body) (let-star-free clauses body))
         ((list 'quote arg) nil)
         ((guard (list 'quasiquote arg) (consp arg))
            (free-in-quasiquote arg))
         ((list 'quasiquote arg) nil)
         ((guard x (listp x))
           (reduce #'union (mapcar #'free form)))))

(defun free-union (forms)
    (reduce #'union (mapcar #'free forms)))

(defun free-in-quasiquote (forms)
    (reduce #'union
            (loop for i in forms
                  collect (match i
                                 ((list 'unquote x) (free x))
                                 ((list 'unquote-splicing x) (free x))
                                 ((guard x (atom x)) nil)
                                 (otherwise (free-in-quasiquote i))))))

(defun alpha (form alist)
   (cond ((eq (car form) 'lambda)
          (list 'lambda
                (mapcar (lambda (i)
                             (let ((it (assoc i alist)))
                                  (if it (cdr it) i)))
                        (second form))
                (mysubst alist (third form))))))



(defun formal-arguments-p (obj)
   (and (listp obj)
        (map-and (lambda (i)
                     (and (symbolp i) (not (member i '(lambda quote let)))))
                 obj)))

(defun check-syntax-list (lst original-lst success failure)
   (cond ((null lst) (funcall success))
         ((atom lst) (funcall failure original-lst))
         (t (check-syntax (car lst)
               (lambda ()
                   (check-syntax-list (cdr lst) original-lst success failure))
               failure))))

(defun check-cond-syntax (lst original-form success failure)
   (cond ((null lst) (funcall success))
         ((atom lst) (funcall failure original-form))
         ((not (listp (car lst))) (funcall failure original-form))
         ((not (= (length (car lst)) 2)) (funcall failure original-form))
         (t (check-syntax (caar lst)
                    (lambda ()
                        (check-syntax (second (car lst))
                                (lambda ()
                                    (check-cond-syntax (cdr lst) original-form success failure))
                                failure))
                    failure))))

(defun check-let-syntax (lst original-form success failure)
      (cond ((null lst) (check-syntax (third original-form) success failure))
            ((atom lst) (funcall failure original-form))
            ((not (listp (car lst))) (funcall failure original-form))
            ((not (symbolp (caar lst))) (funcall failure original-form))
            ((not (= (length (car lst)) 2)) (funcall failure original-form))
            (t (check-syntax (second (car lst))
                             (lambda ()
                                     (check-let-syntax (cdr lst) original-form success failure))
                             failure))))

(defun check-syntax (form success failure)
    (cond ((eq form 'lambda) (funcall failure form))
          ((eq form 'quote) (funcall failure form))
          ((atom form) (funcall success))
          ((eq (car form) 'lambda)
             (if (and (= (length form) 3)
                      (formal-arguments-p (second form)))
                 (check-syntax (third form) success failure)
                 (funcall failure form)))
          ((eq (car form) 'quote)
             (if (= (length form) 2)
                 (funcall success)
                 (funcall failure form)))
          ((eq (car form) 'cond)
            (check-cond-syntax (cdr form) form success failure))
          ((eq (car form) 'quasiquote)
            (match form
                   ((list 'quasiquote (list 'unquote x)) (funcall failure form))
                   ((list 'quasiquote (list 'unquote-splicing x)) (funcall failure form))
                   (otherwise (funcall success))))   ; рекурсия должна быть
          ((or (eq (car form) 'let) (eq (car form) 'let*))
           (if (= (length form) 3)
               (check-let-syntax (second form) form success failure)
               (funcall failure form)))
          ((listp form) (check-syntax-list form form success failure))))

; ------------- STRUCTURAL PREDICATES ----------------

(defun quoted-p (obj)
    (and (listp obj) (eq (car obj) 'quote)))

(defun quoted-symbol-p (obj)
    (and (quoted-p obj) (symbolp (second obj))))

(defun quoted-list-p (obj)
    (and (quoted-p obj) (listp (second obj))))

(defun quasiquoted-list-p (obj)
    (and (listp obj) (eq (car obj) 'quasiquote) (listp (second obj))))

(defun fraction-p (obj)
    (and (listp obj)
         (eq (car obj) '/)
         (= (length obj) 3)
         (numberp (second obj))
         (numberp (third obj))))

; ------------- STRUCTURAL PREDICATES ----------------
;------------------- END -----------------------------

(defstruct funcall-cont fun evaled unevaled)

;normalize (form k n)
(defun normalize-list-of-forms (unevaled evaled k n)
  ;  (format t "formas: ~a acc: ~a~%" forms acc)
    (cond ((null unevaled)
           (apply-function (reverse evaled) k n))
          ((normal-form-p (car unevaled))
           (normalize-list-of-forms (cdr unevaled) (cons (car unevaled) evaled) k n))
          (t (normalize (car unevaled)
                        (cons (make-funcall-cont :evaled evaled :unevaled (cdr unevaled))
                              k)
                        n))))

(defstruct if-cont exp1 exp2)

(defun normalize-if (expr k n)
    (match expr
           ((list 'if 'true arg2 arg3) (evaluate arg2 k n "SPECIAL OPERATOR: IF"))
           ((list 'if 'false arg2 arg3) (evaluate arg3 k n "SPECIAL OPERATOR: IF"))
           ((guard (list 'if arg1 arg2 arg3) (not (normal-form-p arg1)))
                (normalize arg1
                           (cons (make-if-cont :exp1 arg2 :exp2 arg3)
                                 k)
                           n))
           (otherwise (stop-computation k expr n))))

(defstruct cond-cont clauses value)

(defun evaluate (expr k n rule)
    (if (normal-form-p expr)
        (apply-continuation k expr n rule)
        (progn
            (print-trace k expr n rule)
            (normalize expr k (1+ n)))))

(defun normalize-cond (expr k n)
    (match expr
       ((list* 'cond (list 'true value) clauses)
          (evaluate value k n "SPECIAL OPERATOR: COND"))
       ((list* 'cond (list 'false value) clauses)
          (evaluate `(cond ,@clauses) k n "SPECIAL OPERATOR: COND"))
       ((guard (list* 'cond (list condition value) clauses)
               (not (normal-form-p condition)))
         (normalize condition
                    (cons (make-cond-cont :value value :clauses clauses)
                          k)
                    n))
       (otherwise (stop-computation k expr n))))

(defstruct let-cont evaled unevaled vars body)

(defun normalize-let (unevaled evaled vars body k n)
     (cond ((null unevaled)
            (evaluate (beta-reduction
                            body
                            (loop for i in (reverse evaled)
                                  for j in vars
                                  collect (cons j i)))
                       k n "SPECIAL OPERATOR: LET"))
           ((normal-form-p (car unevaled))
            (normalize-let (cdr unevaled) (cons (car unevaled) evaled) vars body k n))
           (t (normalize (car unevaled)
                         (cons (make-let-cont :evaled evaled
                                              :unevaled (cdr unevaled)
                                              :vars vars
                                              :body body)
                               k)
                         n))))

(defun transform-let* (var val clauses expr)
     `(let* ,(loop for i in clauses
                   collect (list (car i)
                                 (beta-reduction (second i) (list (cons var val)))))
            ,(beta-reduction expr (list (cons var val)))))

(defstruct let-star-cont var clauses body)

(defun normalize-let* (clauses expr k n)
      (cond ((null clauses) (evaluate expr k n "SPECIAL OPERATOR: LET*"))
            ((normal-form-p (second (car clauses)))
             (evaluate (transform-let* (caar clauses) (second (car clauses)) (cdr clauses) expr)
                       k n "SPECIAL OPERATOR: LET*"))
            (t (normalize (second (car clauses))
                          (cons (make-let-star-cont :var (caar clauses)
                                                    :clauses (cdr clauses)
                                                    :body expr)
                                k)
                          n))))

; -------------- CONS, CAR, CDR, LIST ---------------

(defun move-elem-into-quasiquote (elem)
    (match elem
           ((list 'quote x) x)
           ((list 'quasiquote x) x)
           ((guard x (numberp x)) x)
           (otherwise `(unquote ,elem))))

(defun apply-list (exp k n)
     (apply-continuation k
          (if (map-and #'data-p (cdr exp))
              `(quote ,(loop for i in (cdr exp) collect (drop-quote-if-needed i)))
              `(quasiquote ,(mapcar #'move-elem-into-quasiquote (cdr exp))))
          n "FUNCTION: LIST"))

(defun apply-cons (exp k n)
    (match exp
           ((list 'cons elem (list 'quasiquote lst))
            (apply-continuation k `(quasiquote (,(move-elem-into-quasiquote elem) ,@lst)) n "FUNCTION: CONS"))
           ((list 'cons (list 'quote elem) (list 'quote lst))
            (apply-continuation k `(quote (,elem ,@lst)) n "FUNCTION: CONS"))
           ((list 'cons (list 'quasiquote elem) (list 'quote lst))
            (apply-continuation k `(quasiquote (,elem ,@lst))) n "FUNCTION: CONS")
           ((guard (list 'cons elem (list 'quote lst)) (data-p elem))
            (apply-continuation k `(quote (,elem ,@lst)) n "FUNCTION: CONS"))
           ((list 'cons elem (list 'quote lst))
            (apply-continuation k `(quasiquote ((unquote ,elem) ,@lst)) n "FUNCTION: CONS"))
           (otherwise (stop-computation k exp n))))

(defun apply-car (exp k n)
    (match exp
           ((list 'car (list 'quote (cons first rest)))
            (apply-continuation k (add-quote-if-needed first) n "FUNCTION: CAR"))
           ((list 'car (list 'quasiquote (cons (list 'unquote first) rest)))
            (apply-continuation k first n "FUNCTION: CAR"))
           ((list 'car (list 'quasiquote (cons first rest)))
            (apply-continuation k (add-quasiquote-if-needed first) n "FUNCTION: CAR"))
           (otherwise (stop-computation k exp n))))

(defun apply-cdr (exp k n)
    (match exp
           ((list 'cdr (list 'quote (cons first rest)))
            (apply-continuation k `(quote ,rest) n "FUNCTION: CDR"))
           ((list 'cdr (list 'quasiquote (cons first rest)))
            (apply-continuation k (add-quasiquote-if-needed rest) n "FUNCTION: CDR"))
           (otherwise (stop-computation k exp n))))

; -------------- CONS, CAR, CDR, LIST ---------------
; --------------------- END -------------------------


; ------------------- QUASIQUOTE --------------------


(defun contains-unquoted-not-in-normal-form (tree)
      (cond ((atom tree) nil)
            ((eq 'unquote (car tree)) (not (normal-form-p (second tree))))
            ((eq 'unquote-splicing (car tree)) (not (normal-form-p (second tree))))
            (t (map-or #'contains-unquoted-not-in-normal-form tree))))

(defun find-unquote (value rest)
      (match value
             ((guard x (atom x)) nil)
             ((guard (list 'unquote x) (not (normal-form-p x))) (values value rest))
             ((list 'unquote x) 42)
             ((guard (list 'unquote-splicing x) (not (normal-form-p x))) (values value rest))
             ((list 'unquote-splicing x) nil)
             (otherwise (find-unquote-in-list value nil rest))))

(defun find-unquote-in-list (lst acc rest)
      (cond ((null lst) nil)
            ((contains-unquoted-not-in-normal-form (car lst))
             (find-unquote (car lst) (cons (list acc (cdr lst)) rest)))
            (t (find-unquote-in-list (cdr lst) (append acc (list (car lst))) rest))))

(defun form-unquote (res cont)
   (cond ((null cont) res)
         (t (form-unquote `(,@(first (car cont)) ,res ,@(second (car cont)))
                          (cdr cont)))))

(defun quasiqote-element-to-str (x)
   (match x
          ((list 'unquote z) (format nil ",~a" (to-str z)))
          ((list 'unquote-splicing z) (format nil ",@~a" (to-str z)))
          (otherwise (green (to-str x)))))


(defun quasiquote-result-to-str (res context)
   (cond ((eq 'unquote context) (format nil ",~a" res))
         ((eq 'unquote-splicing context) (format nil ",@~a" res))
         (t (errro "bad argumet to quasiquote-result-to-str"))))

(defun unquote-cont-to-str (res cont context)
   (cond ((null cont) (concatenate 'string (green "`") res))
         (t (unquote-cont-to-str (concatenate 'string
                                    (green "(")
                                    (concatenate-with-right-space
                                        (mapcar #'quasiqote-element-to-str (first (car cont))))
                                    (quasiquote-result-to-str res context)
                                    (concatenate-with-left-space
                                        (mapcar #'quasiqote-element-to-str (second (car cont))))
                                    (green ")"))
                                (cdr cont)
                                context))))

(defun concatenate-with-right-space (lst)
   (if (null lst)
       ""
       (concatenate 'string (car lst) " " (concatenate-with-right-space (cdr lst)))))


(defun concatenate-with-left-space (lst)
   (if (null lst)
       ""
       (concatenate 'string " " (car lst) (concatenate-with-left-space (cdr lst)))))

(defun add-unquote-if-needed (elem unquote)
    (match elem
           ((list 'quote x) x)
           ((list 'quasiquote x) x)
           ((guard x (numberp x)) x)
           (otherwise `(,unquote ,elem))))

(defun contains (tree x)
   (cond ((null tree) nil)
         ((equal x tree) t)
         ((atom tree) nil)
         (t (map-or (lambda (i) (contains i x)) tree))))

(defun contains-bad-unquote-splicing (tree)
     (match tree
            ((guard x (atom x)) nil)
            ((guard (list 'unquote-splicing (list 'quote x)) (listp x)) nil)
            ((guard (list 'unquote-splicing (list 'quasiquote x)) (listp x)) nil)
            ((list 'unquote-splicing x) t)
            (otherwise (map-or #'contains-bad-unquote-splicing tree))))


(defun optimize-quasiquote-element (tree)
    (match tree
           ((guard x (atom x)) (list x))
           ((guard (list 'unquote x) (numberp x)) (list x))
           ((list 'unquote (list 'quote x)) (list x))
           ((list 'unquote (list 'quasiquote x)) (list x))
           ((list 'unquote x) (list tree))
           ((list 'unquote-splicing (list 'quote x)) x)
           ((list 'unquote-splicing (list 'quote x)) x)
           ((list 'unquote-splicing (list 'quasiquote x)) x)
           ((list 'unquote-splicing x) (list tree))
           (otherwise (list (loop for i in tree append (optimize-quasiquote-element i))))))

(defun optimize-quasiquote (tree)
    (add-quasiquote-if-needed (loop for i in tree append (optimize-quasiquote-element i))))

(defun contains-unquote (tree)
   (cond ((atom tree) nil)
         ((eq 'unquote (car tree)) t)
         ((eq 'unquote-splicing (car tree)) t)
         (t (map-or #'contains-unquote tree))))

(defun add-quasiquote-if-needed (tree)
     (cond ((numberp tree) tree)
           ((stringp tree) tree)
           ((contains-unquote tree) `(quasiquote ,tree))
           (t `(quote ,tree))))

; ------------------- QUASIQUOTE --------------------
; ---------------------- END ------------------------
;(list '* (list '/ a b) (list '/ c d))
;              ((list '* (list '/ a b) c)
;                  (apply-continuation k `(/ ,(* a c) ,b) n))
;              ((list '* c (list '/ a b))
;                  (apply-continuation k `(/ ,(* a c) ,b) n))))


(defun reduce-fraction (a b)
    (let* ((g (gcd a b))
           (denominator (/ b g))
           (numerator (/ a g)))
          (cond ((= denominator 1) (/ a g))
                ((< denominator 0) `(/ ,(- numerator) ,(- denominator)))
                (t `(/ ,numerator ,denominator)))))

(defun numerator* (fraction)
    (match fraction
           ((list '/ a b) a)
           (otherwise (error "ill-formaed fraction"))))

(defun denominator* (fraction)
    (match fraction
           ((list '/ a b) b)
           (otherwise (error "ill-formaed fraction"))))

(defun apply-plus (exp k n)
   (match exp
          ((guard (list '+ a b) (and (numberp a) (numberp b)))
           (apply-continuation k (+ a b) n "FUNCTION: +"))
          ((guard (list '+ a (list '/ c d)) (numberp a))
           (apply-continuation k (reduce-fraction (+ (* a d) c) d) n "FUNCTION: +"))
          ((guard (list '+ (list '/ a b) c) (numberp c))
           (apply-continuation k (reduce-fraction (+ a (* b c)) b) n "FUNCTION: +"))
          ((list '+ (list '/ a b) (list '/ c d))
           (apply-continuation k (reduce-fraction (+ (* a d) (* b c)) (* b d)) n "FUNCTION: +"))
          (otherwise (stop-computation k exp n))))

(defun apply-mul (exp k n)
   (match exp
          ((guard (list '* a b) (and (numberp a) (numberp b)))
           (apply-continuation k (* a b) n "FUNCTION: *"))
          ((guard (list '* a (list '/ c d)) (numberp a))
           (apply-continuation k (reduce-fraction (* a c) d) n "FUNCTION: *"))
          ((guard (list '* (list '/ a b) c) (numberp c))
           (apply-continuation k (reduce-fraction (* a c) b) n "FUNCTION: *"))
          ((list '* (list '/ a b) (list '/ c d))
           (apply-continuation k (reduce-fraction (* a c) (* b d)) n "FUNCTION: *"))
          (otherwise (stop-computation k exp n))))

(defun apply-minus (exp k n)
   (match exp
          ((guard (list '- a b) (and (numberp a) (numberp b)))
           (apply-continuation k (- a b) n "FUNCTION: -"))
          ((guard (list '- a (list '/ c d)) (numberp a))
           (apply-continuation k (reduce-fraction (- (* a d) c) d) n "FUNCTION: -"))
          ((guard (list '- (list '/ a b) c) (numberp c))
           (apply-continuation k (reduce-fraction (- a (* b c)) b) n "FUNCTION: -"))
          ((list '- (list '/ a b) (list '/ c d))
           (apply-continuation k (reduce-fraction (- (* a d) (* b c)) (* b d)) n "FUNCTION: -"))
          (otherwise (stop-computation k exp n))))

(defun apply-div (exp k n)
    (match exp
           ((list '/ a 0) (stop-computation k exp n))
           ((list '/ a 1) (apply-continuation k a n "FUNCTION: /"))
           ((guard (list '/ a b) (and (numberp a) (numberp b)))
            (apply-continuation k (reduce-fraction a b) n "FUNCTION: /"))
           ((guard (list '/ a (list '/ c d)) (numberp a))
            (apply-continuation k (reduce-fraction (* a d) c) n "FUNCTION: /"))
           ((guard (list '/ (list '/ a b) c) (numberp c))
            (apply-continuation k (reduce-fraction a (* b c)) n "FUNCTION: /"))
           ((list '/ (list '/ a b) (list '/ c d))
            (apply-continuation k (reduce-fraction (* a d) (* b c)) n "FUNCTION: /"))
           (otherwise (stop-computation k exp n))))


(defun apply-comparisons (f a b)
    (cond ((and (numberp a) (numberp b)) (convert-bool (funcall f a b)))
          ((and (fraction-p a) (fraction-p b)) (compare-fractions f a b))
          ((and (fraction-p a) (numberp b)) (compare-fractions f a (list '/ b 1)))
          ((and (numberp a) (fraction-p b)) (compare-fractions f (list '/ a 1) b))))

; compare fractions by cross-multiplying
(defun compare-fractions (fn a b)
      (convert-bool (funcall fn (* (numerator* a) (denominator* b))
                                (* (denominator* a) (numerator* b)))))

(defun apply-less-then (exp k n)
      (match exp
             ((list '< a b) (apply-continuation k (apply-comparisons #'< a b)  n "FUNCTION: <"))
             (otherwise (stop-computation k exp n))))

(defun apply-greater-then (exp k n)
      (match exp
             ((list '> a b) (apply-continuation k (apply-comparisons #'> a b)  n "FUNCTION: >"))
             (otherwise (stop-computation k exp n))))

(defun apply-less-then-or-equal (exp k n)
      (match exp
             ((list '<= a b) (apply-continuation k (apply-comparisons #'< a b)  n "FUNCTION: <="))
             (otherwise (stop-computation k exp n))))

(defun apply-greater-then-or-equal (exp k n)
      (match exp
             ((list '>= a b) (apply-continuation k (apply-comparisons #'> a b)  n "FUNCTION: >="))
             (otherwise (stop-computation k exp n))))


(defun apply-fraction-arithmetic (op a b c d)
    (cond ((eq '* op) (reduce-fraction (* a c) (* b d)))
          ((eq '+ op) (reduce-fraction (+ (* a d) (* b c)) (* b d)))
          ((eq '- op) (reduce-fraction (- (* a d) (* b c)) (* b d)))
          ((eq '/ op) (reduce-fraction (* a d) (* b c)))))


          ;       ----------------- STRING OPERATIONS ---------------------
        ;                ((guard (list 'string-append arg1 arg2) (and (stringp arg1) (stringp arg2)))
        ;                 (apply-continuation k (concatenate 'string arg1 arg2) n))
        ;                ((guard (list 'subseq str arg)
        ;                        (and (stringp str) (numberp arg) (< arg (length str))))
        ;                  (apply-continuation k (subseq str arg) n))
        ;                ((guard (list 'subseq str arg1 arg2)
        ;                        (and (stringp str) (numberp arg1) (numberp arg2) (< arg2 (length str)) (> arg1 0)))
        ;                  (apply-continuation k (subseq str arg1 arg2) n))

(defun apply-lambda (body formals actuals k n)
     (evaluate (beta-reduction
                        body
                        (loop for i in formals
                              for j in actuals
                              collect (cons i j)))
               k n (format nil "FUNCTION: (LAMBDA ~a …)" formals)))


(defun apply-numberp (exp k n)
      (match exp
             ((list 'numberp arg)
              (convert-bool (or (numberp arg) (fraction-p arg)) n "FUNCTION: NUMBERP"))
             (otherwise (stop-computation k exp n))))

(defun apply-symbolp (exp k n)
      (match exp
             ((list 'symbolp (list 'quote x)) 'true n "FUNCTION: SYMBOLP")
             ((list 'symbolp x) 'false n "FUNCTION: SYMBOLP")
             (otherwise (stop-computation k exp n))))

(defun apply-null (exp k n)
      (match exp
             ((guard (list 'null (list 'quote lst)) (listp lst))
              (apply-continuation k (convert-bool (null lst)) n "FUNCTION: NULL"))
             ((guard (list 'null (list 'quasiquote lst)) (listp lst))
              (apply-continuation k (convert-bool (null lst)) n "FUNCTION: NULL"))
             (otherwise (stop-computation k exp n))))


(defun apply-equality (exp k n)
      (match exp
             ((guard (list '= a b) (and (numberp a) (numberp b)))
              (apply-continuation k (convert-bool (= a b)) n "FUNCTION: ="))
             ((guard (list '= a b) (and (fraction-p a) (fraction-p b)))
              (apply-continuation k (convert-bool (equal a b)) n "FUNCTION: ="))
             ((list '= (list 'quote a) (list 'quote b))
              (apply-continuation k (convert-bool (equal a b)) n "FUNCTION: ="))
             ((list '= 'true 'true) (apply-continuation k 'true n "FUNCTION: ="))
             ((list '= 'false 'false) (apply-continuation k 'true n "FUNCTION: ="))
             (t 'false)))

(defparameter builtins (make-hash-table))

(setf (gethash '+ builtins) #'apply-plus)
(setf (gethash '- builtins) #'apply-minus)
(setf (gethash '* builtins) #'apply-mul)
(setf (gethash '/ builtins) #'apply-div)
(setf (gethash 'car builtins) #'apply-car)
(setf (gethash 'cdr builtins) #'apply-cdr)
(setf (gethash 'null builtins) #'apply-null)
(setf (gethash 'cons builtins) #'apply-cons)
(setf (gethash '<= builtins) #'apply-less-then-or-equal)
(setf (gethash '>= builtins) #'apply-greater-then-or-equal)
(setf (gethash '< builtins) #'apply-less-then)
(setf (gethash '> builtins) #'apply-greater-then)
(setf (gethash 'numberp builtins) #'apply-numberp)
(setf (gethash 'symbolp builtins) #'apply-symbolp)
(setf (gethash '= builtins) #'apply-equality)
(setf (gethash 'list builtins) #'apply-list)




(defun apply-function (exp k n)
   (match exp
          ((guard (cons f args) (and (symbolp f) (gethash f builtins)))
           (multiple-value-bind (fun is-there) (gethash f builtins)
             (if is-there
                 (funcall fun exp k n)
                 (stop-computation k exp n))))
          ((guard (cons (list 'lambda formals body) actuals)
                  (= (length formals) (length actuals)))
           (apply-lambda body formals actuals k n))
          ((guard (cons f args) (assoc f *glob-env*))
              (let ((funct (cdr (assoc f *glob-env*))))
                   (if (= (length (second funct)) (length args))
                       (evaluate (beta-reduction (third funct)
                                                 (loop for i in (second funct)
                                                       for j in args
                                                       collect (cons i j)))
                                 k n (format nil "FUNCTION: ~a" f))
                       (stop-computation k exp n))))
          (otherwise (stop-computation k exp n))))


(defun convert-bool (bool) (if bool 'TRUE 'FALSE))


(defun normalize (form k n)
       (match form
              ((guard x (normal-form-p x)) (apply-continuation k x n "NORMAL FORM (TO BE DELETED)"))
              ((guard (list 'quote arg) (is-quote-unnecessary arg))
                 (apply-continuation k arg n "SPECIAL OPERATOR: QUOTE"))
              ((list 'quasiquote arg)
                (multiple-value-bind (unq body) (find-unquote arg '())
                ;     (print unq) (terpri)
                     (cond (unq (normalize (second unq)
                                           (cons (make-quasiquote-cont :subst unq :body body)
                                                 k)
                                           n))
                           ((contains-bad-unquote-splicing arg) (stop-computation k form n))
                           (t (apply-continuation k (optimize-quasiquote arg) n "SPECIAL OPERATOR: QUASIQUOTE")))))
             ((list* 'cond args) (normalize-cond form k n))
             ((list* 'if args) (normalize-if form k n))
             ((list 'let clauses body) (normalize-let (mapcar #'second clauses)
                                                      '()
                                                      (mapcar #'first clauses)
                                                      body k n))
             ((list 'let* clauses body) (normalize-let* clauses body k n))
             ((cons fun args)
                 (normalize-list-of-forms form nil k n))
              (otherwise (stop-computation k form n))))

(defstruct quasiquote-cont subst body)

; исключить из окружения переменные лямбда-списка
(defun exclude-variables (vars env)
    (cond ((null env) nil)
          ((member (caar env) vars) (exclude-variables vars (cdr env)))
          (t (cons (car env) (exclude-variables vars (cdr env))))))

(defun replace-in-list (lst env)
     (loop for i in lst
           collect (let ((tmp (assoc i env))) (if tmp (cdr tmp) i))))

(defun replace-in-clauses (clauses env)
     (loop for i in clauses
           collect (let ((tmp (assoc (car i) env)))
                        (if tmp (list (cdr tmp) (second i))
                                i))))

(defun dangerous-substitutions (lambda-list env)
     (loop for i in env when (intersection lambda-list (free (cdr i)))
                        collect i))

(defun reduce-lambda-with-alpha (formals body env)
    (let* ((dangerous-env (dangerous-substitutions formals env))
           (vars-to-be-renamed (mapcar #'cdr dangerous-env))
           (new-vars (loop for i in vars-to-be-renamed
                           collect (gentemp)))
           (new-vars-env (pairlis vars-to-be-renamed new-vars))
           (new-formals (replace-in-list formals new-vars-env)))
          (beta-reduction
                   `(lambda ,new-formals ,(beta-reduction body new-vars-env))
                   env)))

(defun reduce-let-and-let*-with-alpha (l clauses body env)
    (let* ((dangerous-env (dangerous-substitutions (mapcar #'car clauses) env))
           (vars-to-be-renamed (mapcar #'cdr dangerous-env))
           (new-vars (loop for i in vars-to-be-renamed
                           collect (gentemp)))
           (new-vars-env (pairlis vars-to-be-renamed new-vars))
           (new-clauses (replace-in-clauses clauses new-vars-env)))
          (beta-reduction
                   (list l new-clauses
                         (beta-reduction body new-vars-env))
                   env)))

(defun member-let (var clauses)
    (cond ((null clauses) nil)
          ((eq (caar clauses) var) t)
          (t (member var (cdr clauses)))))
#|
(defun simple-beta-reduction-one-var (tree var subst)
     (match tree
            (nil nil)
            ((guard x (and (symbolp x) (eq x var))) subst)
            ((guard x (atom x)) x)
            ((list 'quote arg) tree)
            ((guard (list 'lambda formals body)
                    (member var formals))
              tree)
            ((guard (list 'lambda formals body)
                    (member var (free subst)))
              ....
            ((guard (list (or 'let let*) clauses body)
                    (member-let var clauses))
             (list (car tree)
                   (loop for i in clauses
                         collect (list (car i) (simple-beta-reduction-one-var (second i) var subst)))
                   body))
            ((list (or 'let let*) clauses body)
               (list (car tree)
                     (loop for i in clauses
                           collect (list (car i) (simple-beta-reduction-one-var (second i) var subst)))
                     (simple-beta-reduction-one-var body var subst)))
            ((list 'quasiquote x)
               (list 'quasiquote (substitute-in-quasiquote-simple-one-var var subst)))
            (otherwise
               (mapcar (lambda (i) (beta-reduction i env)) tree))))

(defun substitute-in-quasiquote-simple-one-var (tree var subst)
    (match tree
           ((guard x (atom x)) x)
           ((list 'unquote x) (list 'unquote (simple-beta-reduction-one-var var subst)))
           ((list 'unquote-splicing x) (list 'unquote-splicing (simple-beta-reduction-one-var var subst)))
           (otherwise (loop for i in tree collect (substitute-in-quasiquote-simple-one-var i var subst)))))
|#
(defun beta-reduction (tree env)
   (match tree
          (nil nil)
          ((guard x (and (symbolp x) (assoc x env)))
           (cdr (assoc x env)))
          ((guard x (atom x)) x)
          ((list 'quote arg) tree)
          ((guard (list 'lambda formals body)
                  (dangerous-substitutions formals env))
              (reduce-lambda-with-alpha formals body env))
          ((list 'lambda formals body)
                  (list 'lambda
                        formals
                        (beta-reduction body (exclude-variables formals env))))
          ((guard (list l clauses body)
                  (and (member l '(let let*))
                       (dangerous-substitutions (mapcar #'first clauses) env)))
              (reduce-let-and-let*-with-alpha l clauses body env))
          ((guard (list l clauses body) (member l '(let let*)))
              (list l (loop for i in clauses
                            collect (list (car i) (beta-reduction (second i) env)))
                      (beta-reduction body (exclude-variables (mapcar #'car clauses) env))))
          ((list 'quasiquote x)
             (list 'quasiquote (substitute-in-quasiquote x env)))
          (otherwise
              (mapcar (lambda (i) (beta-reduction i env)) tree))))

#| Изначально была идея оптимизировать quasiqote после подстановки прямо в функции
подстановки, однако в дальнейшем решено было отказаться от этого. Процедура опитимизации
предполагает возможность ошибки (т.е. она является полупредикатом из-за unquote-splicing),
тогда как подстановка -- это обычная функция. Кроме того, непонятно на каком основании
оптимизируются только quasiqote при подстановке, ведь можно представить подстановку с одновременным
вычислением встроенных функций. Вообщем этих двух причин достаточно, чтобы не идти по пути опитимизации
(удаления излишних unquote и unquote-splicing) во время подстановки.|#
(defun substitute-in-quasiquote (tree env)
    (match tree
           ((guard x (atom x)) x)
           ((list 'unquote x) (list 'unquote (beta-reduction x env)))
           ((list 'unquote-splicing x) (list 'unquote-splicing (beta-reduction x env)))
           (otherwise (loop for i in tree collect (substitute-in-quasiquote i env)))))


(defun stepper (expr)
   (if (normal-form-p expr)
       (format t "NORMAL FORM: ~a~%~%" (to-str expr))
       (normalize expr nil 1)))


(defun eval-repl-command (expr)
   (match expr
          ((guard (list 'defun name formals body)
                  (and (symbolp name)
                       (formal-arguments-p formals)))
            (push (cons name `(lambda ,formals ,body)) *glob-env*)
            (format t "FUNCTION ~a DEFINED~%" name)
            (repl))
          ((list 'show 'rules) (format t "~a~%" *rules*)
                               (repl))
          ((list 'trace 'on) (setq trace-flag 'on) (repl))
          ((list 'trace 'off) (setq trace-flag 'off) (repl))
          ((list 'trace 'stack) (setq trace-flag 'stack) (repl))
          ((list 'dir) (format t "BUILT-IN FUNCTIONS: ~a~%" (to-str (alexandria:hash-table-keys builtins)))
                       (repl))
          (otherwise
            (check-syntax expr
                (lambda ()
                       (if *trace-time-flag*
                           (time (stepper expr))
                           (stepper expr))
                       (repl))
                (lambda (form*)
                    (format t "SYNTAX ERROR: ~a~%~%" form*)
                    (repl))))))

(defun to-str (obj)
    (match obj
           ('lambda "λ")
           ((guard x (or (numberp x) (equal x 'true) (equal x 'false)))
            (green (format nil "~a" x)))
           ((list 'quote x) (green (format nil "'~a" (to-bland-str x))))
           ((list 'quasiquote x) (format nil "~a~a" (green "`") (quasiquote-to-str x)))
           (nil "()")
           ((guard x (stringp x)) (green (format nil "\"~a\"" x)))
           ((guard x (consp x)) (format nil "(~a)" (tail-to-str x)))
           (otherwise (format nil "~a" obj))))

(defun to-str-reduced (obj)
    (match obj
           ((guard x (or (numberp x) (equal x 'true) (equal x 'false)))
            (red (format nil "~a" x)))
           ((list 'quote x) (red (format nil "'~a" (to-bland-str x))))
           ((list 'quasiquote x) (format nil "~a~a" (red "`") (quasiquote-to-str x)))
           (nil (red "()"))
           ((guard x (consp x)) (format nil "~a~a~a" (red "(") (tail-to-str x) (red ")")))
           ((guard x (eq nil-atom x)) (red "NIL"))
           (otherwise (red (format nil "~a" obj)))))


(defun tail-to-str (lst)
    (cond ((null lst) "")
          ((null (cdr lst)) (format nil "~a" (to-str (car lst))))
          (t (format nil "~a ~a" (to-str (car lst)) (tail-to-str (cdr lst))))))

(defun tail-to-str-with-left-space (lst)
    (if (null lst)
        ""
        (format nil " ~a~a" (to-str (car lst)) (tail-to-str-with-left-space (cdr lst)))))

(defun tail-to-str-with-right-space (lst)
    (if (null lst)
        ""
        (format nil "~a ~a" (to-str (car lst)) (tail-to-str-with-right-space (cdr lst)))))

(defun to-bland-str (obj)
     (cond ((consp obj) (format nil "(~a)" (tail-to-bland-str obj)))
           ((stringp obj) (format nil "\"~a\"" obj))
           ((null obj) "()")
           ((eq nil-atom obj) "NIL")
           (t (format nil "~a" obj))))

(defun tail-to-bland-str (lst)
    (cond ((null lst) "")
          ((null (cdr lst)) (format nil "~a" (to-bland-str (car lst))))
          (t (format nil "~a ~a" (to-bland-str (car lst)) (tail-to-bland-str (cdr lst))))))

(defun quasiquote-to-str (obj)
     (match obj
            ((list 'unquote x) (format nil ",~a" (to-str x)))
            ((list 'unquote-splicing x) (format nil ",@~a" (to-str x)))
            ((guard x (consp obj))
              (format nil "~a~a~a" (green "(") (quasiquote-tail-to-str obj) (green ")")))
            ((guard x (stringp obj)) (green (format nil "\"~a\"" obj)))
            (nil (green "()"))
            ((guard x (eq nil-atom obj)) (green "NIL"))
            (otherwise (green (format nil "~a" obj)))))

(defun quasiquote-tail-to-str (lst)
     (cond ((null lst) "")
           ((null (cdr lst)) (format nil "~a" (quasiquote-to-str (car lst))))
           (t (format nil "~a ~a" (quasiquote-to-str (car lst)) (quasiquote-tail-to-str (cdr lst))))))


(defun substitute-in-continuation (v k)
     (cond ((funcall-cont-p k)
            (format nil "(~a~a~a)"
               (tail-to-str-with-right-space (reverse (funcall-cont-evaled k)))
               v
               (tail-to-str-with-left-space (funcall-cont-unevaled k))))
           ((let-cont-p k)
               (format nil "(LET (~{~a~^ ~}) ~a)"
                   (loop for i in (mapcar #'to-str (let-cont-vars k))
                         for j in (append (mapcar #'to-str (reverse (let-cont-evaled k)))
                                          (list v)
                                          (mapcar #'to-str (let-cont-unevaled k)))
                         collect (format nil "(~a ~a)" i j))
                   (to-str (let-cont-body k))))
           ((if-cont-p k)
              (format nil "(IF ~a ~a ~a)"
                     v (to-str (if-cont-exp1 k)) (to-str (if-cont-exp2 k))))
           ((cond-cont-p k)
              (format nil "(COND (~a ~a)~a)"
                      v (to-str (cond-cont-value k))
                      (tail-to-str-with-left-space (cond-cont-clauses k))))
           ((let-star-cont-p k)
              (format nil "(LET* ((~a ~a)~a) ~a)"
                      (let-star-cont-var k)
                      v
                      (tail-to-str-with-left-space (let-star-cont-clauses k))
                      (let-star-cont-body k)))
           ((quasiquote-cont-p k)
              (unquote-cont-to-str v (quasiquote-cont-body k) (first (quasiquote-cont-subst k))))
           (t (error "unknown continuation"))))



(defun compose-dump (v k)
    (cond ((null k) v)
          (t (compose-dump (substitute-in-continuation v (car k)) (cdr k)))))

(defun print-trace (k res n rule)
   (case trace-flag
         (stack (format t "~a~%~{~a~^, ~}~%"
                     (yellow (format nil "-----------STEP ~a, ~a" n rule))
                     (cons (to-str res)
                             (loop for i in k
                                   collect (substitute-in-continuation "◯ " i)))))
         (on (format t "~a~%~a~%"
                       (yellow (format nil "-----------STEP ~a, ~a" n rule))
                       (compose-dump (to-str-reduced res) k)))))


(defun apply-continuation (k res n rule)
   (print-trace k res n rule)
   (cond ((null k) (format t "NORMAL FORM: ~a~%~%" (to-str res)))
         ((funcall-cont-p (car k))
          (normalize-list-of-forms
               (funcall-cont-unevaled (car k))
               (cons res (funcall-cont-evaled (car k)))
               (cdr k)
               (1+ n)))
         ((let-cont-p (car k))
          (normalize-let
               (let-cont-unevaled (car k))
               (cons res (let-cont-evaled (car k)))
               (let-cont-vars (car k))
               (let-cont-body (car k))
               (cdr k)
               (1+ n)))
         ((if-cont-p (car k)) (normalize-if `(if ,res
                                                 ,(if-cont-exp1 (car k))
                                                 ,(if-cont-exp2 (car k)))
                                            (cdr k) (1+ n)))
         ((cond-cont-p (car k)) (normalize-cond `(cond (,res ,(cond-cont-value (car k)))
                                                       ,@(cond-cont-clauses (car k)))
                                                (cdr k) (1+ n)))
         ((let-star-cont-p (car k)) (normalize-let* `((,(let-star-cont-var (car k)) ,res)
                                                      ,@(let-star-cont-clauses (car k)))
                                                    (let-star-cont-body (car k))
                                                    (cdr k) (1+ n)))
         ((quasiquote-cont-p (car k))
           (normalize
                `(quasiquote ,(form-unquote `(,(first (quasiquote-cont-subst (car k))) ,res)
                                            (quasiquote-cont-body (car k))))
                (cdr k) (1+ n)))
         (t (error "something is off with applying continuation"))))

(defun stop-computation (k res n)
     (format t "~a ~a~%~%" (red "IRREDUCIBLE FORM:") (compose-dump (to-str-reduced res) k)))

(defun repl ()
    (princ "NORMALIZE: ")
    (finish-output)
    (multiple-value-bind
        (str missing-p)
        (read-line *standard-input* nil "")
        (if missing-p
            (format t "~%KEEP CALM AND REDUCE!~%")
            (read-sexpr str
                        (lambda (v rest)
                            (if (verify-end-of-expr rest)
                                (eval-repl-command v)
                                (progn (format t "Syntax error: something is off~%unread characters: ~a~%" rest)
                                       (repl))))
                        (lambda (msg)
                            (format t "~a~%" msg)
                            (repl))))
         (finish-output)))

(defparameter logo "Reduction-based LISP. Developed by by Popov Roman in 2018.
Inspired by John McCarthy and Brian Cantwell Smith.~%")

(defun main ()
    (format t logo)
    (match *posix-argv*
           ((list name-of-the-interpreter filename) (repl-with-file filename))
           ((list name-of-the-interpreter) (repl))
           (otherwise (format t "BAD COMMAND LINE PARAMETERS:~%"))))

(defun check-file-syntax (lst success failure)
    (if (null lst)
        (funcall success)
        (match (car lst)
               ((guard (list 'defun name args body)
                       (and (symbolp name) (formal-arguments-p args)))
                (check-syntax
                      body
                      (lambda () (check-file-syntax (cdr lst) success failure))
                      failure))
               (otherwise (funcall failure (car lst))))))

(defun define-functions (lst)
    (loop for i in lst do (progn
          ;   (format t "~a~%" i)
            (match i
                  ((guard (list 'defun name args body)
                         (and (symbolp name) (formal-arguments-p args)))
                   (push (cons (second i) `(lambda ,args ,body)) *glob-env*))
                  (otherwise (format t "ERROR in DEFINITION: ~a~%" (to-str i))))))
    (format t "DEFINED FUNCTIONS: ~a~%" (to-bland-str (loop for i in lst collect (second i)))))

(defun repl-with-file (file)
   (if (probe-file file)
       (let ((s (alexandria:read-file-into-string file)))
            (read-bare-list
                    s
                    nil
                    (lambda (v rest)
                        (check-file-syntax
                              v
                              (lambda () (define-functions v))
                              (lambda (msg) (format t "ERROR WHILE LOADING FILE ~a: ~a~%" file msg)))
                        (repl))
                    (lambda (msg)
                            (format t "~a~%" msg)
                            (repl))))
       (format t "THERE IS NO FILE NAMED ~a~%" file)))


(main)
