
(in-package :cxx)

;; bool remove_package(char *pack_name)
(defcfun ("remove_package" remove-c-package) :bool
  (name :string))

;; bool clcxx_init(void (*error_handler)(char *),
;;                      void (*reg_data_callback)(MetaData *, uint8_t))
(defcfun ("clcxx_init" clcxx-init) :bool
  (err-callback :pointer)
  (reg-data-callback :pointer))

;; bool register_lisp_package(const char *cl_pack,
;;                                  void (*regfunc)(clcxx::Package &))
(defcfun ("register_package" register-package) :bool
  (name :string)
  (pack-ptr :pointer))

;; size_t used_bytes_size();
(defcfun ("used_bytes_size" number-of-allocated-bytes) :size)

;; size_t max_stack_bytes_size();
(defcfun ("max_stack_bytes_size" max-stack-bytes-size) :size)

;; bool delete_string(char *string);
(defcfun ("delete_string" destruct-string) :bool
  (string-to-be-deleted :string))


(defun symbols-list (arg-types &optional (method-p nil) (class-obj nil))
  "Return a list of symbols '(V0 V1 V2 V3 ...)
   representing the number of args"
  (let ((m-obj (if  method-p `(obj ,(read-from-string  class-obj))))
        (lst (if arg-types (loop for i in (split-string-by arg-types #\+)
                              for j from 0
				 collect (intern (concatenate 'string "V" (write-to-string j)))))))
    (when (and (not method-p) class-obj)
      (setf lst (nconc lst (list (read-from-string "cl:&optional")
				 (read-from-string "(class nil)")
				 (read-from-string "cl:&rest")
				 (read-from-string "rest")))))
    (if method-p
        (if lst (append (list m-obj) lst) (list m-obj))
        lst)))

(defun compound-type-list (type &optional (array-p nil))
  "Returns a list of strings representing compound type"
  (declare (type string type))
  (let* ((string (string-trim "(" type))
         (str (get-parenthes-string string))
         (lst (append (split-string-by
                       (string-trim ")"
                                    (remove-string str string))
                       #\space) (list str))))
    (if str (progn (if array-p (rotatef (nth 1 lst) (nth 2 lst)))
                   lst)
        (split-string-by (string-trim ")" string) #\space))))

(defun parse-type (type)
  "Returns cffi-type as a keyword
      or list of keywords"
  (declare (string type))
  (if (equal (subseq type 0 1) "(")
      ;; compound type
      (cond ((if (>= (length type) 7) (equal (subseq type 0 7) "(:array") nil)
             (mapcar #'parse-type (compound-type-list type t)))
            ((if (>= (length type) 9) (equal (subseq type 0 9) "(:pointer") nil)
             (mapcar #'parse-type (compound-type-list type)))
            ((if (>= (length type) 11) (equal (subseq type 0 11) "(:reference") nil)
             (mapcar #'parse-type (compound-type-list type)))
            ((if (>= (length type) 17) (equal (subseq type 0 17) "(:const-reference") nil)
             (mapcar #'parse-type (compound-type-list type)))
            ((if (>= (length type) 9) (equal (subseq type 0 9) "(:complex") nil)
             (mapcar #'parse-type (compound-type-list type)))
            ((if (>= (length type) 8) (equal (subseq type 0 8) "(:struct") nil)
             (mapcar #'parse-type (compound-type-list type)))
            ((if (>= (length type) 7) (equal (subseq type 0 7) "(:class") nil)
             (mapcar #'parse-type (compound-type-list type)))
            (t (error "Unkown type : ~S" type)))
      ;; simple type
      (read-from-string type)))

(defun cffi-type (type)
  "Returns cffi-type as a keyword
      or list of keywords"
  (declare (type string type))
  (let ((parsed-type (parse-type type)))
    (if (listp parsed-type) (ecase (first parsed-type)
                              (:array (append (list (second parsed-type)) (list :count)  (list (third parsed-type))))
                              (:complex :pointer)
                              (:pointer (if (equal (second parsed-type)
                                                   :char)
                                            :string
                                            :pointer))
                              (:reference :pointer)
                              (:const-reference :pointer) ;; TODO:add const
                              (:class :pointer)
                              (:struct parsed-type))
        parsed-type)))


(defun parse-args (arg-types &optional (input-type-p t))
  "return argument types (with variables if they are inputs) in a proper list"
  (if input-type-p (if arg-types (loop
                                    for i in (split-string-by arg-types #\+)
                                    for sym in (symbols-list arg-types)
                                    as type = (cffi-type i) then (cffi-type i)
                                    append
                                      (let* ((parsed-type (parse-type i))
                                             (name (cond
                                                     ;; in class
                                                     ((and (listp parsed-type)
                                                           (second parsed-type)
                                                           (equal (first parsed-type) :class)) (second parsed-type))
                                                     ;; in class reference
                                                     ((and (listp parsed-type)
                                                           (if (listp (second parsed-type)) (second (second  parsed-type)))
                                                           (if (listp parsed-type) (or (equal (first parsed-type) :reference)
                                                                                       (equal (first parsed-type) :const-reference)))
                                                           (if (listp (second parsed-type)) (equal (first (second  parsed-type)) :class)))
                                                      (second (second  parsed-type))))))
                                        (if (listp type) `( ,type ,sym)
                                            `( ,type ,(if name `(cxx-ptr ,sym)
                                                          sym)))))
                       nil)
      (let ((type (cffi-type arg-types)))
        (list type))))

(defvar *stream* nil)
(defvar *exports* nil)
(defvar *pack-name* nil)

(declaim (inline make-exports-in-funtion))
(defun make-exports-in-funtion (name)
  ;; don't export functions starting with '%'
  (when (and *stream* (not (equal #\% (char name 0))))
    (eval `(setf *exports* (append *exports* (list ',(read-from-string name))))))
  (when (and (not *stream*) (not (equal #\% (char name 0))))
    (eval `(export ',(read-from-string (concatenate 'string "'" name)) ',(read-from-string *pack-name*)))))

(declaim (inline make-defparameter-function-ptr))
(defun make-defparameter-function-ptr (name ptr)
  `,(if *stream*
       `(defparameter ,name nil)
       `(defparameter ,name ,ptr)))

(defun parse-function (meta-ptr)
  "Returns the function def."
  (with-foreign-slots ((name method-p class-obj func-ptr arg-types return-type) meta-ptr (:struct function-info))
    (let ((f-arg-types (if method-p
                           (left-trim-string-to arg-types #\+)
                           arg-types))
	  (name-func-ptr (read-from-string (concatenate 'string "*" name "-func-ptr*"))))
      (make-exports-in-funtion name)
      `(progn
	 ,(make-defparameter-function-ptr name-func-ptr func-ptr)	 
         (,(if method-p
               'defmethod
               'defun)

           ,(read-from-string name) ,(symbols-list f-arg-types method-p class-obj)
           ;; TODO: add declare type
           ,(let ((return-val
                   `(cffi:foreign-funcall-pointer
                     ,name-func-ptr
                     nil
                     ,@(if method-p
                           ;; cxx-ptr defined in defclass
                           (append '(:pointer (cxx-ptr obj)) (parse-args f-arg-types))
                           (parse-args f-arg-types))
                     ,@(parse-args return-type nil))))
              ;; Wrap return class
              (let* ((parsed-type (parse-type return-type))
                     (objT (cond
                             ;; constructor
                             ((and (not method-p) class-obj)
                              (read-from-string class-obj))
                             ;; return class
                             ((and (listp parsed-type)
                                   (second parsed-type)
                                   (equal (first parsed-type) :class)) (second parsed-type))
                             ;; return class reference
                             ((and (listp parsed-type)
                                   (if (listp (second parsed-type)) (second (second  parsed-type)))
                                   (if (listp (second parsed-type)) (equal (first (second  parsed-type)) :class))
                                   (if (listp parsed-type) (or (equal (first parsed-type) :reference)
                                                               (equal (first parsed-type) :const-reference))))
                              (second (second  parsed-type))))))
                (cond
                  ;; add finalizer to class object
                  (objT
		   (let ((destruct-ptr (read-from-string
					(concatenate 'string
						     "destruct-ptr-"
						     (string objT)))))
		     `(let* ((ptr ,return-val)
			     (initargs (append '(:cxx-ptr) (list ptr)))
			     (ename-class (if ,(read-from-string "class") ,(read-from-string "class") ',objT)))
			(when rest
			  (setf initargs (append rest initargs)))
			(let ((obj (handler-case
				       (apply #'make-instance ename-class (values initargs))
				     (error (err)
				       (,destruct-ptr ptr)
				       (error err)))))
			(tg:finalize obj (lambda ()
					   (,destruct-ptr ptr)))
			obj))))
                  ;; add finalizer to string
                  ((equal parsed-type :string+ptr)
                   `(let* ((val ,return-val)
                           (str (car val))
                           (ptr (cadr val)))
                      (tg:finalize str
                                   (lambda ()
                                     (cxx:destruct-string ptr)))
                   str))
                  ;; non-class return type
                  (t return-val)))))))))

(defun parse-super-classes (s)
  "Returns super class as symbols in a list"
  (if s (loop
           for i in (split-string-by s #\+)
           collect (read-from-string i))))

(defun parse-class-slots (slot-names slot-types)
  "Returns super class as symbols in a list"
  (loop
     ;; TODO: use solt type and define set,get
     for name in (split-string-by slot-names #\+)
     for type in (split-string-by slot-types #\+)
     collect (read-from-string name)))

(defun parse-cstruct-slots (slot-names slot-types)
  "Returns super class as symbols in a list"
  (loop
     for name in (split-string-by slot-names #\+)
     for type in (split-string-by slot-types #\+)
     collect (list name (cffi-type type))))

(declaim (inline make-exports-in-class))
(defun make-exports-in-class (name constructor)
  ;;added due to issues with specialists
  (if *stream*
      (eval `(setf *exports* (append *exports* (list ',(read-from-string name)))))
      (eval `(export ',(read-from-string (concatenate 'string "'" name)) ',(read-from-string *pack-name*))))
  (when (not (cffi:null-pointer-p constructor))
    (if *stream*
	(eval `(setf *exports* (append *exports* (list ',(read-from-string (concatenate 'string "create-" name))))))
	(eval `(export ',(read-from-string (concatenate 'string "'create-" name)) ',(read-from-string *pack-name*))))))

(defun parse-class (meta-ptr)
  "Define class"
  (with-foreign-slots ((name super-classes slot-names slot-types constructor destructor) meta-ptr (:struct class-info))
    (if (cffi:null-pointer-p destructor) ;; c struct
        `(cffi:defcstruct ,(read-from-string name)
             ,@(if slot-types (parse-cstruct-slots slot-names slot-types)))
	(let ((d-name-pointer (read-from-string (concatenate 'string "*destruct-ptr-" name "*"))))
	  (make-exports-in-class name constructor)
	  `(progn
	     (defclass ,(read-from-string name) ,(parse-super-classes super-classes)
	       ((cxx-class-ptr
		 :accessor cxx-ptr
		 :initarg :cxx-ptr
		 :initform (required "Use Class constructor function.")))
	       ;; TODO: add slots
	       ;; ,@(if slot-types (parse-class-slots slot-names slot-types)))
	       (:documentation "Cxx class stored in lisp"))
	     
	     ,(make-defparameter-function-ptr d-name-pointer destructor)     
	     (defun ,(read-from-string
                    (concatenate 'string "destruct-ptr-" name)) (class-ptr)
             "delete class pointer"
             (if (not  (cffi:null-pointer-p class-ptr))
                 (cffi:foreign-funcall-pointer ,d-name-pointer
                                               nil :pointer class-ptr
                                                   :void)))

           ,(if (not (cffi:null-pointer-p  constructor))
                (let ((m-name (read-from-string (concatenate 'string "create-" name)))
                      (destruct-ptr (read-from-string
                                     (concatenate 'string
                                                  "destruct-ptr-"
                                                  name)))
		      (construct-ptr (read-from-string
				      (concatenate 'string
						   "*"
						   name
						   "-default-constructor-ptr*"))))
                  `(progn
                     ,(make-defparameter-function-ptr construct-ptr constructor)
                     (defun ,m-name (cl:&optional (class nil) cl:&rest rest)
                       "create class with default constructor"
                       (let* ((ptr (cffi:foreign-funcall-pointer
                                    ,construct-ptr nil :pointer))
			      (initargs (append '(:cxx-ptr) (list ptr)))
			      (ename-class (if ,(read-from-string "class") ,(read-from-string "class") ',(read-from-string name))))
			 (when rest
			   (setf initargs (append rest initargs)))
			 (let ((obj (handler-case (apply #'make-instance ename-class (values initargs))
				      (error (err) (,destruct-ptr ptr)
					(error err)))))
			   (tg:finalize obj (lambda ()
					      (,destruct-ptr ptr)))
			   obj)))))))))))


(defun parse-constant (meta-ptr)
  "Define constant"
  (with-foreign-slots ((name value) meta-ptr (:struct constant-info))
    `(progn
       (export ',(read-from-string name))
       (defconstant ,(read-from-string name)
         ,(read-from-string value)))))

;; inline void lisp_error(const char *error)
(defcallback lisp-error :void ((err :string))
  (format t "Caught error: ~a~%" err))

;; void send_data(MetaData *M, uint8_t n)
(defcallback reg-data :void ((meta-ptr :pointer) (type :uint8))
  (ecase type
    (0
     ;; (print "class")
     ;; (print (parse-class meta-ptr))
     (eval (parse-class meta-ptr)))

    (1
     ;; (print "constant")
     ;; (print (parse-constant meta-ptr))
     (eval (parse-constant meta-ptr)))

    (2
     ;; (print "function")
     ;; (print (parse-function meta-ptr))
     (eval (parse-function meta-ptr)))))


(defvar *file-stream* nil)

;; Init. clcxx
(defun init ()
  (setf *exports* nil)
  (setf *file-stream* nil)
  (clcxx-init (callback lisp-error) (callback reg-data)))

(defun cxx-make-package (pack-name)
  (progn (when (not (find-package pack-name))
      (make-package pack-name)
      (use-package 'cl pack-name))
  (eval `(progn
	   (in-package ,pack-name)
	   (import 'cxx::cxx-ptr)
	   (export 'cxx-ptr)))))

(defun close-file-stream ()
  (when *exports*
    (let ((*print-case* :downcase))
      (format *file-stream* "~%~%(export '~a)" *exports*)
      (setf *exports* nil)))
  (when (streamp *file-stream*)
    (progn
      (close *file-stream*)
      (setf *file-stream* nil))))

(defun add-package (pack-name func-name)
  "Register lisp package with pack-name
            from func-name defined in ClCxx lib"
  (declare (type string pack-name func-name))
  (setf *pack-name* pack-name) 
  (let ((curr-pack (package-name *package*)))
    (unwind-protect
	 (progn
	   (cxx-make-package pack-name)
	   (register-package pack-name (foreign-symbol-pointer func-name))
	   (close-file-stream))
      (eval `(in-package ,curr-pack)))))

(defun remove-package (pack-name)
  (if (remove-c-package pack-name)
      (delete-package pack-name)))

;; *********** Generate common lisp files ****************

;; void send_data(MetaData *M, uint8_t n) 
(defcallback reg-data-stream :void ((meta-ptr :pointer) (type :uint8))
  (let ((*print-case* :downcase))
    (ecase type
      (0
	 (setf *stream* t)
	 (print (parse-class meta-ptr) *file-stream*)
	 (setf *stream* nil)
	 (eval (parse-class meta-ptr)))

	(1
	 (print (parse-constant meta-ptr) *file-stream*)
	 (eval (parse-constant meta-ptr)))

	(2
	 (setf *stream* t)
	 (print (parse-function meta-ptr) *file-stream*)
	 (setf *stream* nil)
	 (eval (parse-function meta-ptr))))))

(defun init-generate-lisp-code (file-name pack-name)
  (setf *exports* '(cxx-ptr))
  (setf *file-stream* (open file-name :direction :output :if-exists :supersede :if-does-not-exist :create))
  (format *file-stream* "(cl:when (not (cl:find-package ~@:(~S~)))~%  (cl:make-package ~@:(~S~))~%" pack-name pack-name)
  (format *file-stream* "  (cl:use-package 'cl '~a))~%~%(cl:in-package :~a)~%~%"  pack-name pack-name)
  (format *file-stream* "(import 'cxx::cxx-ptr)~%")
  (clcxx-init (callback lisp-error) (callback reg-data-stream)))

(defun parse-function-pointer (meta-ptr)
  "Set the pointers to c++ functions."
  (with-foreign-slots ((name func-ptr) meta-ptr (:struct function-info))
    (let ((name-func-ptr (read-from-string (concatenate 'string "*" name "-func-ptr*"))))
      `(setf ,name-func-ptr ,func-ptr))))

(defun parse-class-pointer (meta-ptr)
  "Set pointers to c++ class constructor and destructor"
  (with-foreign-slots ((name constructor destructor) meta-ptr (:struct class-info))
    (let ((d-name-pointer (read-from-string (concatenate 'string "*destruct-ptr-" name "*")))
	  (constructor-ptr (read-from-string (concatenate 'string "*" name "-default-constructor-ptr*"))))
      `(progn
	 (setf ,d-name-pointer ,destructor)
	 ,(when (not (cffi:null-pointer-p  constructor))
	    `(setf ,constructor-ptr ,constructor))))))

;; void send_data(MetaData *M, uint8_t n)
(defcallback reg-data-cxx-wrap-ptr :void ((meta-ptr :pointer) (type :uint8))
  (ecase type
    (0
     (eval (parse-class-pointer meta-ptr)))

    (1
     ;; (print "constant")
     nil)

    (2
     (eval (parse-function-pointer meta-ptr)))))

(defun init-cxx-wrap-ptr ()
  (setf *exports* nil)
  (setf *file-stream* nil)
  (clcxx-init (callback lisp-error) (callback reg-data-cxx-wrap-ptr)))
