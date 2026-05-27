;; Proof obligation:
;;ASSUME NEW CONSTANT CONSTANT_N_,
;;        NEW CONSTANT CONSTANT_K_,
;;        NEW VARIABLE VARIABLE_x_,
;;        \A CONSTANT_i_ \in 1..CONSTANT_N_ :
;;           ?VARIABLE_x_#prime[CONSTANT_i_]
;;           = ?VARIABLE_x_#prime[CONSTANT_i_ - 1] ,
;;        ?VARIABLE_x_#prime \in [0..CONSTANT_N_ -> 0..CONSTANT_K_ - 1] ,
;;        ?VARIABLE_x_#prime[0] # ?VARIABLE_x_#prime[CONSTANT_N_] ,
;;        ASSUME NEW CONSTANT CONSTANT_f_ \in [0..CONSTANT_N_ ->
;;                                               0..CONSTANT_K_ - 1],
;;               \A CONSTANT_i_ \in 1..CONSTANT_N_ :
;;                  CONSTANT_f_[CONSTANT_i_] = CONSTANT_f_[CONSTANT_i_ - 1] 
;;        PROVE  CONSTANT_f_[0] = CONSTANT_f_[CONSTANT_N_] 
;; PROVE  FALSE
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #167
;;   generated from file "./Dijkstra.tla", line 192, characters 17-18

(set-logic UFNIA)
(declare-sort u 0)
;; Standard TLA+ operators
(declare-fun int2u (Int) u)
(declare-fun u2int (u) Int)
(declare-fun tla__Int () u)
(declare-fun tla__minus (u u) u)
(declare-fun tla__le (u u) Bool)
(declare-fun tla__Range (u u) u)
(declare-fun tla__in (u u) Bool)
(declare-fun tla__emptyset () u)
(declare-fun tla__isAFcn (u) Bool)
(declare-fun tla__DOMAIN (u) u)
(declare-fun tla__fcnapp (u u) u)
(declare-fun tla__unspec (u u) u)

;; Terms, predicates and strings
(declare-fun a_CONSTANTunde_Kunde_a () u)
(declare-fun a_CONSTANTunde_Nunde_a () u)
(declare-fun a_VARIABLEunde_xunde_hash_primea () u)

(assert
  (forall ((X_5 Int)) (! (= (u2int (int2u X_5)) X_5) :pattern ((int2u X_5)))))
(assert
  (forall ((X_5 u))
  (! (= (tla__in X_5 tla__Int) (exists ((N_4 Int)) (= X_5 (int2u N_4)))) :pattern ((tla__in X_5 tla__Int)))))
(assert
  (forall ((M_3 Int) (N_4 Int))
  (! (= (tla__minus (int2u M_3) (int2u N_4)) (int2u (- M_3 N_4))) :pattern ((tla__minus (int2u M_3) (int2u N_4))))))
(assert
  (forall ((M_3 Int) (N_4 Int))
  (! (= (tla__le (int2u M_3) (int2u N_4)) (<= M_3 N_4)) :pattern ((tla__le (int2u M_3) (int2u N_4))))))
(assert
  (forall ((M_3 Int) (N_4 Int) (Z_7 u))
  (=
  (tla__in Z_7 (tla__Range (int2u M_3) (int2u N_4)))
  (exists ((X_5 Int)) (and (= Z_7 (int2u X_5)) (<= M_3 X_5) (<= X_5 N_4))))))
(assert
  (forall ((M_3 Int) (N_4 Int) (X_5 Int) (Y_6 Int))
  (=>
  (and
  (or (<= M_3 N_4) (<= X_5 Y_6))
  (= (tla__Range (int2u M_3) (int2u N_4)) (tla__Range (int2u X_5) (int2u Y_6))))
  (and (= M_3 X_5) (= N_4 Y_6)))))
(assert
  (forall ((M_3 Int) (N_4 Int))
  (= (= (tla__Range (int2u M_3) (int2u N_4)) tla__emptyset) (< N_4 M_3))))
(assert
  (forall ((S_8 u) (T_9 u))
  (=> (forall ((X_5 u)) (= (tla__in X_5 S_8) (tla__in X_5 T_9))) (= S_8 T_9))))
(assert
  (forall ((X_5 u))
  (! (= (tla__in X_5 tla__emptyset) false) :pattern ((tla__in X_5 tla__emptyset)))))
(assert
  (forall ((F_11 u) (G_12 u))
  (=>
  (and
  (tla__isAFcn F_11) (tla__isAFcn G_12)
  (forall ((X_5 u))
  (= (tla__in X_5 (tla__DOMAIN F_11)) (tla__in X_5 (tla__DOMAIN G_12)))))
  (= (tla__DOMAIN F_11) (tla__DOMAIN G_12)))))
(assert
  (forall ((F_11 u) (G_12 u))
  (=>
  (and
  (tla__isAFcn F_11) (tla__isAFcn G_12)
  (= (tla__DOMAIN F_11) (tla__DOMAIN G_12))
  (forall ((X_5 u))
  (=>
  (tla__in X_5 (tla__DOMAIN G_12))
  (= (tla__fcnapp F_11 X_5) (tla__fcnapp G_12 X_5)))))
  (= F_11 G_12))))
(assert (not false))
(assert
  (forall ((a_CONSTANTunde_iunde_a Int))
    (=>
      (and
        (<= 1 a_CONSTANTunde_iunde_a)
        (tla__le (int2u a_CONSTANTunde_iunde_a) a_CONSTANTunde_Nunde_a))
      (=
        (ite
          (<= 0 a_CONSTANTunde_iunde_a)
          (tla__fcnapp
            a_VARIABLEunde_xunde_hash_primea (int2u a_CONSTANTunde_iunde_a))
          (tla__unspec
            a_VARIABLEunde_xunde_hash_primea (int2u a_CONSTANTunde_iunde_a)))
        (ite
          (tla__le
            (int2u (- a_CONSTANTunde_iunde_a 1)) a_CONSTANTunde_Nunde_a)
          (tla__fcnapp
            a_VARIABLEunde_xunde_hash_primea
            (int2u (- a_CONSTANTunde_iunde_a 1)))
          (tla__unspec
            a_VARIABLEunde_xunde_hash_primea
            (int2u (- a_CONSTANTunde_iunde_a 1))))))))
(assert (tla__isAFcn a_VARIABLEunde_xunde_hash_primea))
(assert
  (=
    (tla__DOMAIN a_VARIABLEunde_xunde_hash_primea)
    (tla__Range (int2u 0) a_CONSTANTunde_Nunde_a)))
(assert
  (forall ((a_v1a u))
    (=>
      (and
        (tla__in a_v1a tla__Int) (tla__le (int2u 0) a_v1a)
        (tla__le a_v1a a_CONSTANTunde_Nunde_a))
      (and
        (tla__in
          (tla__fcnapp a_VARIABLEunde_xunde_hash_primea a_v1a) tla__Int)
        (tla__le
          (int2u 0) (tla__fcnapp a_VARIABLEunde_xunde_hash_primea a_v1a))
        (tla__le
          (tla__fcnapp a_VARIABLEunde_xunde_hash_primea a_v1a)
          (tla__minus a_CONSTANTunde_Kunde_a (int2u 1)))))))
(assert
  (not
    (=
      (ite
        (tla__le (int2u 0) a_CONSTANTunde_Nunde_a)
        (tla__fcnapp a_VARIABLEunde_xunde_hash_primea (int2u 0))
        (tla__unspec a_VARIABLEunde_xunde_hash_primea (int2u 0)))
      (ite
        (and
          (tla__in a_CONSTANTunde_Nunde_a tla__Int)
          (tla__le (int2u 0) a_CONSTANTunde_Nunde_a)
          (tla__le a_CONSTANTunde_Nunde_a a_CONSTANTunde_Nunde_a))
        (tla__fcnapp a_VARIABLEunde_xunde_hash_primea a_CONSTANTunde_Nunde_a)
        (tla__unspec a_VARIABLEunde_xunde_hash_primea a_CONSTANTunde_Nunde_a)))))
(assert
  (forall ((a_CONSTANTunde_funde_a u))
    (=>
      (and
        (tla__isAFcn a_CONSTANTunde_funde_a)
        (=
          (tla__DOMAIN a_CONSTANTunde_funde_a)
          (tla__Range (int2u 0) a_CONSTANTunde_Nunde_a))
        (forall ((a_v2a u))
          (=>
            (and
              (tla__in a_v2a tla__Int) (tla__le (int2u 0) a_v2a)
              (tla__le a_v2a a_CONSTANTunde_Nunde_a))
            (and
              (tla__in (tla__fcnapp a_CONSTANTunde_funde_a a_v2a) tla__Int)
              (tla__le (int2u 0) (tla__fcnapp a_CONSTANTunde_funde_a a_v2a))
              (tla__le
                (tla__fcnapp a_CONSTANTunde_funde_a a_v2a)
                (tla__minus a_CONSTANTunde_Kunde_a (int2u 1))))))
        (forall ((a_CONSTANTunde_iunde_a Int))
          (=>
            (and
              (<= 1 a_CONSTANTunde_iunde_a)
              (tla__le (int2u a_CONSTANTunde_iunde_a) a_CONSTANTunde_Nunde_a))
            (=
              (ite
                (tla__in
                  (int2u a_CONSTANTunde_iunde_a)
                  (tla__DOMAIN a_CONSTANTunde_funde_a))
                (tla__fcnapp
                  a_CONSTANTunde_funde_a (int2u a_CONSTANTunde_iunde_a))
                (tla__unspec
                  a_CONSTANTunde_funde_a (int2u a_CONSTANTunde_iunde_a)))
              (ite
                (tla__in
                  (int2u (- a_CONSTANTunde_iunde_a 1))
                  (tla__DOMAIN a_CONSTANTunde_funde_a))
                (tla__fcnapp
                  a_CONSTANTunde_funde_a (int2u (- a_CONSTANTunde_iunde_a 1)))
                (tla__unspec
                  a_CONSTANTunde_funde_a (int2u (- a_CONSTANTunde_iunde_a 1))))))))
      (=
        (ite
          (tla__in (int2u 0) (tla__DOMAIN a_CONSTANTunde_funde_a))
          (tla__fcnapp a_CONSTANTunde_funde_a (int2u 0))
          (tla__unspec a_CONSTANTunde_funde_a (int2u 0)))
        (ite
          (tla__in
            a_CONSTANTunde_Nunde_a (tla__DOMAIN a_CONSTANTunde_funde_a))
          (tla__fcnapp a_CONSTANTunde_funde_a a_CONSTANTunde_Nunde_a)
          (tla__unspec a_CONSTANTunde_funde_a a_CONSTANTunde_Nunde_a))))))

(check-sat)
(exit)
