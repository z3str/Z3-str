(declare-variable s String)
(declare-variable ret0 String)
(declare-variable ret1 String)


(assert (= ret0 (Replace (Replace s "<"  "&lt;")  ">"  "&gt;") ) )

(assert (= ret1 (Concat ret0 "<br/>") ) )

(assert (= s "<script type = \"text/javascript\">") )

(check-sat)
(get-model)