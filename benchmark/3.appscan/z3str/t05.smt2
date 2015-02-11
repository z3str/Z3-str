


(declare-fun cookie () String)
(declare-fun cookie_part1 () String)
(declare-fun cookie_part2 () String)
(declare-fun cookie_part3 () String)
(declare-fun lang () String)
(declare-fun idx1 () Int)
(declare-fun len1 () Int)
(declare-fun l1 () String)



(assert (= cookie  (Concat cookie_part1 (Concat cookie_part2 cookie_part3) ) ) )

(assert (RegexIn cookie_part2 (RegexConcat (RegexConcat (RegexUnion (Str2Reg "?") (Str2Reg ";") ) 
                                                        (Str2Reg "searchLang=") ) 
                                           (RegexStar (RegexUnion (Str2Reg "a") (RegexUnion (Str2Reg "b") (RegexUnion (Str2Reg "c") (RegexUnion (Str2Reg "d") (RegexUnion (Str2Reg "e") (RegexUnion (Str2Reg "f") (RegexUnion (Str2Reg "g") (RegexUnion (Str2Reg "h") (RegexUnion (Str2Reg "i") (RegexUnion (Str2Reg "j") (RegexUnion (Str2Reg "k") (RegexUnion (Str2Reg "l") (RegexUnion (Str2Reg "m") (Str2Reg "n") ) ) ) ) ) ) ) ) ) ) ) ) ) ) 
                              )
        )
)

(assert (implies (not (= "" cookie_part3) ) (= cookie_part3 (Concat ";" l1) ) ) )

(assert (> (Length cookie_part2) 11) )

(assert (= cookie "expires=Thu, 18 Dec 2013 12:00:00 UTC;searchLang=nb;domain=local;") )

(assert (= idx1 (+ (Indexof cookie_part2 "=") 1 ) ) )

(assert (= len1 (Length cookie_part2) ) )

(assert (> idx1 0) )

(assert (> len1 idx1))

(assert (= lang (Substring cookie_part2 idx1 (- len1 idx1) ) ) )


(check-sat)
