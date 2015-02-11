


(declare-fun parameter () String)
(declare-fun a () String)
(declare-fun index () Int)
(declare-fun str1 () String)
(declare-fun index1 () Int)
(declare-fun sli () String)
(declare-fun index2 () Int)




(assert (= parameter "eOfferCode") )
(assert (= index (Indexof a parameter) ) )

(assert (ite (not (= index (- 0 1) ) ) 
             (and (= str1 (Substring a index (- (Length a) index) ) ) 
                  (= index1 (Indexof str1 "&") )
                  (ite (= index1 (- 0 1) )
                       (and (= index2 (Indexof str1 "=") )
                            (= sli (Substring str1 (+ index2 1) (- (Length str1) (+ index2 1) ) ) )
                       )
                       (and (= index2 (Indexof str1 "=") )
                            (= sli (Substring str1 (+ index2 1) (- index1 (+ index2 1) ) ) )
                       )
                  )
             )                 
             (= sli "")
        ) 
)

(assert (not (= sli "") ) )


(check-sat)
(get-model)
