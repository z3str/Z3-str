(declare-variable s0 String)
(declare-variable s1 String)
(declare-variable s2 String)
(declare-variable s3 String)
(declare-variable s4 String)
(declare-variable ret String)


(assert (= s1 (Replace s0 "&" "&amp;") )  )

(assert (= s2 (Replace s1 "&nbsp;"  " ") ) )

(assert (= s3 (Replace s2 "\""  "&quot;") ) )

(assert (= s4 (Replace s3 "<"  "&lt;") ) )

(assert (= ret (Replace s4 ">"  "&gt;") ) )


(assert (or (Contains ret "<") (Contains ret ">") ) )

(check-sat)
(get-model)
