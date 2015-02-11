


(declare-fun cookie () String)
(declare-fun cookie_part1 () String)
(declare-fun cookie_part2 () String)
(declare-fun cookie_part3 () String)
(declare-fun t1 () String)
(declare-fun l1 () String)


(assert (= cookie  (Concat (Concat "expires=Thu, 18 Dec 2013 12:00:00 UTC;searchLang=" t1) "domain=www.somesite.com") ) )

(assert (= cookie  (Concat cookie_part1 (Concat cookie_part2 cookie_part3) ) ) )

(assert (RegexIn cookie_part2 (RegexConcat (RegexConcat (RegexUnion (Str2Reg "?") (Str2Reg ";") ) 
                                                        (Str2Reg "searchLang=") ) 
                                           (RegexStar (RegexUnion (Str2Reg "a") (RegexUnion (Str2Reg "b") (RegexUnion (Str2Reg "c") (RegexUnion (Str2Reg "d") (RegexUnion (Str2Reg "e") (RegexUnion (Str2Reg "f") (RegexUnion (Str2Reg "g") (RegexUnion (Str2Reg "h") (RegexUnion (Str2Reg "i") (RegexUnion (Str2Reg "j") (RegexUnion (Str2Reg "k") (RegexUnion (Str2Reg "l") (RegexUnion (Str2Reg "m") (Str2Reg "n") ) ) ) ) ) ) ) ) ) ) ) ) ) ) 
                              )
        )
)

(assert (implies (not (= "" cookie_part3) ) (= cookie_part3 (Concat ";" l1) ) ) )

(assert (> (Length cookie_part2) 12) )

(assert (not (= "" cookie_part1) ) )

(check-sat)
(get-model)

