



(declare-fun src () String)
(declare-fun URL () String)
(declare-fun ret () String)
(declare-fun pred () bool)
(declare-fun p1 () bool)


(assert (= p1 (EndsWith src "_hA") ) )

(assert (= pred  (or (EndsWith src "_ha") (EndsWith src "_Ha") (EndsWith src "_HA") p1 ) ) )

(assert (ite (not (= src "") ) 
             (ite pred
                  (= ret src)
                  (= ret (Concat src "_ha") )
             )     
             (ite (> (Indexof URL "www.ha45.com/index.html") (- 0 1) )
                  (= ret "srcindex_ha")
                  (ite (> (Indexof URL "www.ha45.com/index.htm") (- 0 1) )
                       (= ret "srcieak_ha")
                       (ite (> (Indexof URL "www.ha45.com/?vit=fws") (- 0 1) )
                            (= ret "srcvit_ha")
                            (= ret "siteha45")
                       )
                  )
            )
       )
)

(assert (EndsWith ret "_ha") )



(assert (not (= src "") ) )
(check-sat)
