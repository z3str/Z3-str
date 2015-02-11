(declare-variable s String)
(declare-variable ret0 String)
(declare-variable ret1 String)


(assert (= ret0 (Replace (Replace s "<"  "&lt;")  ">"  "&gt;") ) )

(assert (= ret1 (Concat ret0 "<br/>") ) )

(assert (or (Contains ret1 "<") (Contains ret1 ">") ) )


(check-sat)
(get-model)
