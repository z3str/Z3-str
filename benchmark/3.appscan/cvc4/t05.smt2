(set-logic QF_S)
(set-option :produce-models true)

(declare-fun cookie () String)
(declare-fun cookie_part1 () String)
(declare-fun cookie_part2 () String)
(declare-fun cookie_part3 () String)
(declare-fun lang () String)
(declare-fun idx1 () Int)
(declare-fun len1 () Int)
(declare-fun l1 () String)



(assert (= cookie  (str.++ cookie_part1 cookie_part2 cookie_part3) ) ) 

(assert (str.in.re cookie_part2 (re.++ (re.union (str.to.re "?") (str.to.re ";") ) 
                                       (str.to.re "searchLang=")
                                       (re.* (re.union (str.to.re "a") (str.to.re "b") (str.to.re "c") (str.to.re "d") (str.to.re "e") (str.to.re "f") (str.to.re "g") (str.to.re "h") (str.to.re "i") (str.to.re "j") (str.to.re "k") (str.to.re "l") (str.to.re "m") (str.to.re "n") ) )
                                )
        )
)

(assert (=> (not (= "" cookie_part3) ) (= cookie_part3 (str.++ ";" l1) ) ) )

(assert (> (str.len cookie_part2) 11) )

(assert (= cookie "expires=Thu, 18 Dec 2013 12:00:00 UTC;searchLang=nb;domain=local;") )

(assert (= idx1 (+ (str.indexof  cookie_part2  "="  0) 1 ) ) )

(assert (= len1 (str.len cookie_part2) ) )

(assert (> idx1 0) )

(assert (> len1 idx1))

(assert (= lang (str.substr cookie_part2 idx1 (- len1 idx1) ) ) )


(check-sat)
(get-model)

