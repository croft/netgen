(set-option :produce-unsat-cores true) ; enable generation of unsat cores

(declare-var n_0 Int)
(declare-var p_0 Int)
(declare-var n1_0 Int)
(declare-fun cycle (Int Int) Int)
(declare-fun delta (Int Int) Int)
(declare-fun rho (Int Int) Int)

  (assert (and true
       (< 0 n_0)
       (<= n_0 4)
       (<= 0 p_0)
       (<= p_0 3)
       (< 0 n1_0)
       (<= n1_0 4)
       (ite (and (= n_0 1) (= n1_0 2))
                true
                (ite (and (= n_0 1) (= n1_0 3)) true (ite (and (= n_0 2) (= n1_0 4))
                true
                (ite (and (= n_0 3) (= n1_0 4)) true false))))
       true
       (ite (and (= 1 n_0) (= 3 p_0))
            (> (cycle 1 3) (cycle n1_0 3))
            (> (cycle 1 3) (cycle 2 3)))  
       (ite (and (= 2 n_0) (= 3 p_0))
            (> (cycle 2 3) (cycle n1_0 3))
            (> (cycle 2 3) (cycle 4 3)))
       (ite (and (= 3 n_0) (= 3 p_0))
            (> (cycle 3 3) (cycle n1_0 3))
            (> (cycle 3 3) (cycle 4 3)))                  
      ; (= (cycle 3 3) 0)
       (= (cycle 4 3) 0)
     
       (= (delta 11 1) 18)
       (= (delta 11 2) 18)
       (= (delta 11 3) 18)
       (= (delta 11 4) 18)
       (= (delta 13 1) 11)
       (= (delta 13 2) 18)
       (= (delta 13 3) 18)
       (= (delta 13 4) 18)
       (= (delta 14 1) 18)
       (= (delta 14 2) 18)
       (= (delta 14 3) 13)
       (= (delta 14 4) 18)
       (= (delta 18 1) 18)
       (= (delta 18 2) 18)
       (= (delta 18 3) 18)
       (= (delta 18 4) 18)
       (= (delta 19 1) 18)
       (= (delta 19 2) 18)
       (= (delta 19 3) 18)
       (= (delta 19 4) 14)
       
       
       (= (rho 4 3) (delta 19 4))
       (= (rho 1 3) 11) ; final
       
       (ite (and (= 1 n_0) (= 3 p_0))
                (= (rho 1 3) (delta (rho n1_0 3) 1))
                (= (rho 1 3) (delta (rho 2 3) 1)))
       
                
       (ite (and (= 2 n_0) (= 3 p_0))
                (= (rho 2 3) (delta (rho n1_0 3) 2))
                (= (rho 2 3) (delta (rho 4 3) 2)))
                
        (ite (and (= 3 n_0) (= 3 p_0))
                (= (rho 3 3) (delta (rho n1_0 3) 3))
                (= (rho 3 3) (delta (rho 4 3) 3)))
                        
        

      ))
       
       (check-sat)
       (get-model)
     ; (get-unsat-core)
