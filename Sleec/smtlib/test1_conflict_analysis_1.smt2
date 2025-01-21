(set-logic UFLIRA)
(declare-fun C_9_presence () Bool)
(declare-fun B_9_presence () Bool)
(declare-fun Measure_4_presence () Bool)
(declare-fun Measure_3_presence () Bool)
(declare-fun A_13_presence () Bool)
(declare-fun C (Int) Bool)
(declare-fun Measure (Int Int) Bool)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun Measure_5_presence () Bool)
(assert (let ((.def_0 (forall ((Measure_5_time Int)(Measure_5_m1 Int)) (let ((.def_0 (<= 0 Measure_5_time))) (let ((.def_1 (and .def_0 true))) (let ((.def_2 (=> Measure_5_presence .def_1))) (let ((.def_3 (Measure Measure_5_time Measure_5_m1))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((C_9_time Int)) (let ((.def_0 (<= 0 C_9_time))) (let ((.def_1 (=> C_9_presence .def_0))) (let ((.def_2 (C C_9_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((B_9_time Int)) (let ((.def_0 (<= 0 B_9_time))) (let ((.def_1 (=> B_9_presence .def_0))) (let ((.def_2 (B B_9_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((A_13_time Int)) (let ((.def_0 (<= 0 A_13_time))) (let ((.def_1 (=> A_13_presence .def_0))) (let ((.def_2 (A A_13_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (exists ((t_C_7_time Int)) (let ((.def_0 (forall ((C_8_time Int)) (let ((.def_0 (<= C_8_time t_C_7_time))) (let ((.def_1 (C C_8_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_7_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_5 (exists ((t_C_6_time Int)) (let ((.def_0 (forall ((C_7_time Int)) (let ((.def_0 (<= t_C_6_time C_7_time))) (let ((.def_1 (C C_7_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_6_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_6 (and .def_5 .def_4))) (let ((.def_7 (forall ((C_6_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (C C_6_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_8 (or .def_7 .def_6))) (let ((.def_9 (exists ((t_B_6_time Int)) (let ((.def_0 (forall ((B_8_time Int)) (let ((.def_0 (<= B_8_time t_B_6_time))) (let ((.def_1 (B B_8_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_6_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_10 (exists ((t_B_5_time Int)) (let ((.def_0 (forall ((B_7_time Int)) (let ((.def_0 (<= t_B_5_time B_7_time))) (let ((.def_1 (B B_7_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_5_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (forall ((B_6_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (B B_6_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_13 (or .def_12 .def_11))) (let ((.def_14 (exists ((t_A_4_time Int)) (let ((.def_0 (forall ((A_12_time Int)) (let ((.def_0 (<= A_12_time t_A_4_time))) (let ((.def_1 (A A_12_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_4_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_15 (exists ((t_A_3_time Int)) (let ((.def_0 (forall ((A_11_time Int)) (let ((.def_0 (<= t_A_3_time A_11_time))) (let ((.def_1 (A A_11_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_3_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (forall ((A_10_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (A A_10_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (forall ((Measure_3_time Int)(Measure_3_m1 Int)) (let ((.def_0 (forall ((Measure_4_time Int)(Measure_4_m1 Int)) (let ((.def_0 (= Measure_3_presence Measure_4_presence))) (let ((.def_1 (= Measure_3_m1 Measure_4_m1))) (let ((.def_2 (= Measure_3_time Measure_4_time))) (let ((.def_3 (and .def_2 .def_1 .def_0))) (let ((.def_4 (not .def_2))) (let ((.def_5 (or .def_4 .def_3))) (let ((.def_6 (Measure Measure_4_time Measure_4_m1))) (let ((.def_7 (not .def_6))) (let ((.def_8 (or .def_7 .def_5))) .def_8))))))))))))(let ((.def_1 (Measure Measure_3_time Measure_3_m1))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_20 (forall ((A_9_time Int)) (let ((.def_0 (exists ((t_Measure_9_time Int)(t_Measure_9_m1 Int)) (let ((.def_0 (forall ((C_5_time Int)) (let ((.def_0 (+ A_9_time 0))) (let ((.def_1 (<= .def_0 C_5_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ A_9_time 11))) (let ((.def_4 (<= C_5_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (C C_5_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (= A_9_time t_Measure_9_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_9_time t_Measure_9_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_9_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_21 (forall ((A_8_time Int)) (let ((.def_0 (exists ((t_Measure_8_time Int)(t_Measure_8_m1 Int)) (let ((.def_0 (exists ((t_C_5_time Int)) (let ((.def_0 (+ A_8_time 0))) (let ((.def_1 (<= .def_0 t_C_5_time))) (let ((.def_2 (+ A_8_time 15))) (let ((.def_3 (<= t_C_5_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (C t_C_5_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (< t_Measure_8_m1 20))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= A_8_time t_Measure_8_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_8_time t_Measure_8_m1))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (A A_8_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_22 (forall ((B_5_time Int)) (let ((.def_0 (exists ((t_Measure_7_time Int)(t_Measure_7_m1 Int)) (let ((.def_0 (exists ((t_C_4_time Int)) (let ((.def_0 (+ B_5_time 0))) (let ((.def_1 (<= .def_0 t_C_4_time))) (let ((.def_2 (+ B_5_time 7))) (let ((.def_3 (<= t_C_4_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (C t_C_4_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= B_5_time t_Measure_7_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_7_time t_Measure_7_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (B B_5_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_23 (forall ((A_7_time Int)) (let ((.def_0 (exists ((t_Measure_6_time Int)(t_Measure_6_m1 Int)) (let ((.def_0 (exists ((t_B_4_time Int)) (let ((.def_0 (+ A_7_time 0))) (let ((.def_1 (<= .def_0 t_B_4_time))) (let ((.def_2 (+ A_7_time 7))) (let ((.def_3 (<= t_B_4_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (B t_B_4_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= A_7_time t_Measure_6_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_6_time t_Measure_6_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_7_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_24 (exists ((t_B_3_time Int)) (let ((.def_0 (exists ((t_Measure_5_time Int)(t_Measure_5_m1 Int)) (let ((.def_0 (= t_B_3_time t_Measure_5_time))) (let ((.def_1 (Measure t_Measure_5_time t_Measure_5_m1))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (B t_B_3_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_25 (and .def_24 .def_23 .def_22 .def_21 .def_20 .def_19 .def_18 .def_13 .def_8 .def_3 .def_2 .def_1 .def_0))) .def_25)))))))))))))))))))))))))))
(check-sat)
