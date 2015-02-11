(declare-variable s String)
(declare-variable filename_0 String)
(declare-variable filename_1 String)
(declare-variable filename_2 String)
(declare-variable i0 Int)
(declare-variable i1 Int)
(declare-variable i2 Int)
(declare-variable i3 Int)



(assert (= filename_0 s) )

(assert (= i0 (Indexof filename_0 "/") ) )

(assert (ite (not (= i0 (- 0 1) ) )
             (and (= i1 (LastIndexof filename_0 "/") ) 
                  (= i2 (- (Length filename_0) i1) )
                  (= filename_1 (Substring filename_0 i1 i2) )                  
             )
             (= filename_1 filename_0)
        )
)

(assert (= i3 (Indexof filename_1 ".") ) )

(assert (ite (not (= i3 (- 0 1) ) )
             (= filename_2 (Substring filename_1 0 i3) )
             (= filename_2 filename_1)
        ) 
)

(assert (Contains filename_2 "../") )


(check-sat)
(get-model)
