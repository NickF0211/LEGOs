(set-logic UFLIRA)
(declare-fun Measure (Int Int) Bool)
(declare-fun Measure_8_presence () Bool)
(declare-fun C_16_presence () Bool)
(declare-fun B_14_presence () Bool)
(declare-fun Measure_7_presence () Bool)
(declare-fun Measure_6_presence () Bool)
(declare-fun A_18_presence () Bool)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int) Bool)
(assert (let ((.def_0 (forall ((Measure_8_time Int)(Measure_8_m1 Int)) (let ((.def_0 (<= 0 Measure_8_time))) (let ((.def_1 (and .def_0 true))) (let ((.def_2 (=> Measure_8_presence .def_1))) (let ((.def_3 (Measure Measure_8_time Measure_8_m1))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((C_16_time Int)) (let ((.def_0 (<= 0 C_16_time))) (let ((.def_1 (=> C_16_presence .def_0))) (let ((.def_2 (C C_16_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((B_14_time Int)) (let ((.def_0 (<= 0 B_14_time))) (let ((.def_1 (=> B_14_presence .def_0))) (let ((.def_2 (B B_14_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((A_18_time Int)) (let ((.def_0 (<= 0 A_18_time))) (let ((.def_1 (=> A_18_presence .def_0))) (let ((.def_2 (A A_18_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (exists ((t_C_9_time Int)) (let ((.def_0 (forall ((C_15_time Int)) (let ((.def_0 (<= C_15_time t_C_9_time))) (let ((.def_1 (C C_15_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_9_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_5 (exists ((t_C_8_time Int)) (let ((.def_0 (forall ((C_14_time Int)) (let ((.def_0 (<= t_C_8_time C_14_time))) (let ((.def_1 (C C_14_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_8_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_6 (and .def_5 .def_4))) (let ((.def_7 (forall ((C_13_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (C C_13_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_8 (or .def_7 .def_6))) (let ((.def_9 (exists ((t_B_8_time Int)) (let ((.def_0 (forall ((B_13_time Int)) (let ((.def_0 (<= B_13_time t_B_8_time))) (let ((.def_1 (B B_13_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_8_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_10 (exists ((t_B_7_time Int)) (let ((.def_0 (forall ((B_12_time Int)) (let ((.def_0 (<= t_B_7_time B_12_time))) (let ((.def_1 (B B_12_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_7_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (forall ((B_11_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (B B_11_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_13 (or .def_12 .def_11))) (let ((.def_14 (exists ((t_A_7_time Int)) (let ((.def_0 (forall ((A_17_time Int)) (let ((.def_0 (<= A_17_time t_A_7_time))) (let ((.def_1 (A A_17_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_7_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_15 (exists ((t_A_6_time Int)) (let ((.def_0 (forall ((A_16_time Int)) (let ((.def_0 (<= t_A_6_time A_16_time))) (let ((.def_1 (A A_16_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_6_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (forall ((A_15_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (A A_15_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (forall ((Measure_6_time Int)(Measure_6_m1 Int)) (let ((.def_0 (forall ((Measure_7_time Int)(Measure_7_m1 Int)) (let ((.def_0 (= Measure_6_presence Measure_7_presence))) (let ((.def_1 (= Measure_6_m1 Measure_7_m1))) (let ((.def_2 (= Measure_6_time Measure_7_time))) (let ((.def_3 (and .def_2 .def_1 .def_0))) (let ((.def_4 (not .def_2))) (let ((.def_5 (or .def_4 .def_3))) (let ((.def_6 (Measure Measure_7_time Measure_7_m1))) (let ((.def_7 (not .def_6))) (let ((.def_8 (or .def_7 .def_5))) .def_8))))))))))))(let ((.def_1 (Measure Measure_6_time Measure_6_m1))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_20 (forall ((A_14_time Int)) (let ((.def_0 (exists ((t_Measure_11_time Int)(t_Measure_11_m1 Int)) (let ((.def_0 (forall ((C_12_time Int)) (let ((.def_0 (+ A_14_time 0))) (let ((.def_1 (<= .def_0 C_12_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ A_14_time 11))) (let ((.def_4 (<= C_12_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (C C_12_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (= A_14_time t_Measure_11_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_11_time t_Measure_11_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_14_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_21 (forall ((B_10_time Int)) (let ((.def_0 (exists ((t_Measure_10_time Int)(t_Measure_10_m1 Int)) (let ((.def_0 (exists ((t_C_7_time Int)) (let ((.def_0 (+ B_10_time 0))) (let ((.def_1 (<= .def_0 t_C_7_time))) (let ((.def_2 (+ B_10_time 7))) (let ((.def_3 (<= t_C_7_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (C t_C_7_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= B_10_time t_Measure_10_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_10_time t_Measure_10_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (B B_10_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_22 (forall ((A_13_time Int)) (let ((.def_0 (exists ((t_Measure_9_time Int)(t_Measure_9_m1 Int)) (let ((.def_0 (exists ((t_B_6_time Int)) (let ((.def_0 (+ A_13_time 0))) (let ((.def_1 (<= .def_0 t_B_6_time))) (let ((.def_2 (+ A_13_time 7))) (let ((.def_3 (<= t_B_6_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (B t_B_6_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= A_13_time t_Measure_9_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_9_time t_Measure_9_m1))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_13_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_23 (exists ((t_A_5_time Int)) (let ((.def_0 (exists ((t_Measure_8_time Int)(t_Measure_8_m1 Int)) (let ((.def_0 (forall ((C_11_time Int)) (let ((.def_0 (+ t_A_5_time 0))) (let ((.def_1 (<= .def_0 C_11_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_A_5_time 15))) (let ((.def_4 (<= C_11_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (C C_11_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (< t_Measure_8_m1 20))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (= t_A_5_time t_Measure_8_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_8_time t_Measure_8_m1))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (A t_A_5_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_24 (and .def_23 .def_22 .def_21 .def_20 .def_19 .def_18 .def_13 .def_8 .def_3 .def_2 .def_1 .def_0))) .def_24))))))))))))))))))))))))))
(check-sat)
