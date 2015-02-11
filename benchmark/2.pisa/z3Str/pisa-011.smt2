(declare-variable s String)
(declare-variable f String)
(declare-variable ret String)


(assert (= ret (Replace s "<" "&lt;") ) )

(assert (= f (Concat  "jquery.js"  "\"></script>" ) ) )

(assert (= s  (Concat "<script src=\"" f ) ) )

(check-sat)
(get-model)