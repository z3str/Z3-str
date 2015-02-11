(declare-variable s String)
(declare-variable var String)
(declare-variable ret String)


(assert (ite  (or (Contains s "<") (Contains s ">") ) 
              (= ret "x")
              (= ret s)
        ) 
)

(assert (= var (Concat "<scr" "ipt")) )

(assert (Contains s var) )

(assert (not (= ret "x") ) )

(check-sat)
(get-model)