



(declare-fun selKeyword_value () String)
(declare-fun selKeyword_value_trimed () String)
(declare-fun p1 () String)
(declare-fun p2 () String)
(declare-fun p3 () String)


(assert (= selKeyword_value (Concat p1 (Concat p2 p3) ) ) )

(assert (RegexIn  p1  (RegexStar (RegexUnion (Str2Reg " ") (Str2Reg "\t") ) ) ) )

(assert (RegexIn  p3  (RegexStar (RegexUnion (Str2Reg " ") (Str2Reg "\t") ) ) ) )

(assert (not (StartsWith p2 " " ) ) )

(assert (not (StartsWith p2 "\t" ) ) )

(assert (not (EndsWith p2 "\t") ) )

(assert (not (EndsWith p2 " ") ) )

(assert (= selKeyword_value_trimed p2) )


(assert (= "\t \tLxxxx29886 \t" selKeyword_value) )


(check-sat)
(get-model)
