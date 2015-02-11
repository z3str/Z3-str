(set-logic QF_S)
(set-option :produce-models true)


(declare-fun selKeyword_value () String)
(declare-fun selKeyword_value_trimed () String)
(declare-fun p1 () String)
(declare-fun p2 () String)
(declare-fun p3 () String)


(assert (= selKeyword_value (str.++ p1 p2 p3) ) )

(assert (str.in.re  p1  (re.* (re.union (str.to.re " ") (str.to.re "\t") ) ) ) )

(assert (str.in.re  p3  (re.* (re.union (str.to.re " ") (str.to.re "\t") ) ) ) )

(assert (not (str.suffixof " " p2) ) )

(assert (not (str.suffixof "\t" p2) ) )

(assert (not (str.prefixof "\t" p2) ) )

(assert (not (str.prefixof " " p2) ) )

(assert (= selKeyword_value_trimed p2) )


(assert (= "\t \tLxxxx29886 \t" selKeyword_value) )

(check-sat)
(get-model)