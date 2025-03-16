(set-logic UFLIRA)
(declare-fun A_83_presence () Bool)
(declare-fun H_65_presence () Bool)
(declare-fun F_76_presence () Bool)
(declare-fun D_53_presence () Bool)
(declare-fun Measure_30_presence () Bool)
(declare-fun Measure (Int Bool Int Bool) Bool)
(declare-fun A (Int) Bool)
(declare-fun B_66_presence () Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int) Bool)
(declare-fun Measure_32_presence () Bool)
(declare-fun G_87_presence () Bool)
(declare-fun E (Int) Bool)
(declare-fun F (Int) Bool)
(declare-fun G (Int) Bool)
(declare-fun H (Int) Bool)
(declare-fun E_87_presence () Bool)
(declare-fun Measure_31_presence () Bool)
(declare-fun C_118_presence () Bool)
(declare-fun D (Int) Bool)
(assert (let ((.def_0 (forall ((Measure_32_time Int)(Measure_32_ba Bool)(Measure_32_na Int)(Measure_32_bb Bool)) (let ((.def_0 (<= 0 Measure_32_time))) (let ((.def_1 (and .def_0 true true true))) (let ((.def_2 (=> Measure_32_presence .def_1))) (let ((.def_3 (Measure Measure_32_time Measure_32_ba Measure_32_na Measure_32_bb))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((H_65_time Int)) (let ((.def_0 (<= 0 H_65_time))) (let ((.def_1 (=> H_65_presence .def_0))) (let ((.def_2 (H H_65_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((G_87_time Int)) (let ((.def_0 (<= 0 G_87_time))) (let ((.def_1 (=> G_87_presence .def_0))) (let ((.def_2 (G G_87_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((F_76_time Int)) (let ((.def_0 (<= 0 F_76_time))) (let ((.def_1 (=> F_76_presence .def_0))) (let ((.def_2 (F F_76_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (forall ((E_87_time Int)) (let ((.def_0 (<= 0 E_87_time))) (let ((.def_1 (=> E_87_presence .def_0))) (let ((.def_2 (E E_87_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_5 (forall ((D_53_time Int)) (let ((.def_0 (<= 0 D_53_time))) (let ((.def_1 (=> D_53_presence .def_0))) (let ((.def_2 (D D_53_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_6 (forall ((C_118_time Int)) (let ((.def_0 (<= 0 C_118_time))) (let ((.def_1 (=> C_118_presence .def_0))) (let ((.def_2 (C C_118_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_7 (forall ((B_66_time Int)) (let ((.def_0 (<= 0 B_66_time))) (let ((.def_1 (=> B_66_presence .def_0))) (let ((.def_2 (B B_66_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_8 (forall ((A_83_time Int)) (let ((.def_0 (<= 0 A_83_time))) (let ((.def_1 (=> A_83_presence .def_0))) (let ((.def_2 (A A_83_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_9 (exists ((t_H_32_time Int)) (let ((.def_0 (forall ((H_64_time Int)) (let ((.def_0 (<= H_64_time t_H_32_time))) (let ((.def_1 (H H_64_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_32_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_10 (exists ((t_H_31_time Int)) (let ((.def_0 (forall ((H_63_time Int)) (let ((.def_0 (<= t_H_31_time H_63_time))) (let ((.def_1 (H H_63_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_31_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (forall ((H_62_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (H H_62_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_13 (or .def_12 .def_11))) (let ((.def_14 (exists ((t_G_87_time Int)) (let ((.def_0 (forall ((G_86_time Int)) (let ((.def_0 (<= G_86_time t_G_87_time))) (let ((.def_1 (G G_86_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_87_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_15 (exists ((t_G_86_time Int)) (let ((.def_0 (forall ((G_85_time Int)) (let ((.def_0 (<= t_G_86_time G_85_time))) (let ((.def_1 (G G_85_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_86_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (forall ((G_84_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (G G_84_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (exists ((t_F_43_time Int)) (let ((.def_0 (forall ((F_75_time Int)) (let ((.def_0 (<= F_75_time t_F_43_time))) (let ((.def_1 (F F_75_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_43_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_20 (exists ((t_F_42_time Int)) (let ((.def_0 (forall ((F_74_time Int)) (let ((.def_0 (<= t_F_42_time F_74_time))) (let ((.def_1 (F F_74_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_42_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_21 (and .def_20 .def_19))) (let ((.def_22 (forall ((F_73_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (F F_73_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_23 (or .def_22 .def_21))) (let ((.def_24 (exists ((t_E_43_time Int)) (let ((.def_0 (forall ((E_86_time Int)) (let ((.def_0 (<= E_86_time t_E_43_time))) (let ((.def_1 (E E_86_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_43_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_25 (exists ((t_E_42_time Int)) (let ((.def_0 (forall ((E_85_time Int)) (let ((.def_0 (<= t_E_42_time E_85_time))) (let ((.def_1 (E E_85_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_42_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_26 (and .def_25 .def_24))) (let ((.def_27 (forall ((E_84_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (E E_84_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_28 (or .def_27 .def_26))) (let ((.def_29 (exists ((t_D_154_time Int)) (let ((.def_0 (forall ((D_52_time Int)) (let ((.def_0 (<= D_52_time t_D_154_time))) (let ((.def_1 (D D_52_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_154_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_30 (exists ((t_D_153_time Int)) (let ((.def_0 (forall ((D_51_time Int)) (let ((.def_0 (<= t_D_153_time D_51_time))) (let ((.def_1 (D D_51_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_153_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_31 (and .def_30 .def_29))) (let ((.def_32 (forall ((D_50_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (D D_50_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_33 (or .def_32 .def_31))) (let ((.def_34 (exists ((t_C_56_time Int)) (let ((.def_0 (forall ((C_117_time Int)) (let ((.def_0 (<= C_117_time t_C_56_time))) (let ((.def_1 (C C_117_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_56_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_35 (exists ((t_C_55_time Int)) (let ((.def_0 (forall ((C_116_time Int)) (let ((.def_0 (<= t_C_55_time C_116_time))) (let ((.def_1 (C C_116_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_55_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_36 (and .def_35 .def_34))) (let ((.def_37 (forall ((C_115_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (C C_115_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_38 (or .def_37 .def_36))) (let ((.def_39 (exists ((t_B_53_time Int)) (let ((.def_0 (forall ((B_65_time Int)) (let ((.def_0 (<= B_65_time t_B_53_time))) (let ((.def_1 (B B_65_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_53_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_40 (exists ((t_B_52_time Int)) (let ((.def_0 (forall ((B_64_time Int)) (let ((.def_0 (<= t_B_52_time B_64_time))) (let ((.def_1 (B B_64_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_52_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_41 (and .def_40 .def_39))) (let ((.def_42 (forall ((B_63_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (B B_63_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_43 (or .def_42 .def_41))) (let ((.def_44 (exists ((t_A_25_time Int)) (let ((.def_0 (forall ((A_82_time Int)) (let ((.def_0 (<= A_82_time t_A_25_time))) (let ((.def_1 (A A_82_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_25_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_45 (exists ((t_A_24_time Int)) (let ((.def_0 (forall ((A_81_time Int)) (let ((.def_0 (<= t_A_24_time A_81_time))) (let ((.def_1 (A A_81_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_24_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_46 (and .def_45 .def_44))) (let ((.def_47 (forall ((A_80_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (A A_80_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_48 (or .def_47 .def_46))) (let ((.def_49 (forall ((Measure_30_time Int)(Measure_30_ba Bool)(Measure_30_na Int)(Measure_30_bb Bool)) (let ((.def_0 (forall ((Measure_31_time Int)(Measure_31_ba Bool)(Measure_31_na Int)(Measure_31_bb Bool)) (let ((.def_0 (= Measure_30_presence Measure_31_presence))) (let ((.def_1 (= Measure_30_bb Measure_31_bb))) (let ((.def_2 (= Measure_30_na Measure_31_na))) (let ((.def_3 (= Measure_30_ba Measure_31_ba))) (let ((.def_4 (= Measure_30_time Measure_31_time))) (let ((.def_5 (and .def_4 .def_3 .def_2 .def_1 .def_0))) (let ((.def_6 (not .def_4))) (let ((.def_7 (or .def_6 .def_5))) (let ((.def_8 (Measure Measure_31_time Measure_31_ba Measure_31_na Measure_31_bb))) (let ((.def_9 (not .def_8))) (let ((.def_10 (or .def_9 .def_7))) .def_10))))))))))))))(let ((.def_1 (Measure Measure_30_time Measure_30_ba Measure_30_na Measure_30_bb))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_50 (forall ((F_72_time Int)) (let ((.def_0 (exists ((t_Measure_307_time Int)(t_Measure_307_ba Bool)(t_Measure_307_na Int)(t_Measure_307_bb Bool)) (let ((.def_0 (exists ((t_G_85_time Int)) (let ((.def_0 (<= F_72_time t_G_85_time))) (let ((.def_1 (G t_G_85_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (= F_72_time t_Measure_307_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_307_time t_Measure_307_ba t_Measure_307_na t_Measure_307_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (F F_72_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_51 (forall ((H_61_time Int)) (let ((.def_0 (exists ((t_Measure_306_time Int)(t_Measure_306_ba Bool)(t_Measure_306_na Int)(t_Measure_306_bb Bool)) (let ((.def_0 (forall ((F_71_time Int)) (let ((.def_0 (+ H_61_time 0))) (let ((.def_1 (<= .def_0 F_71_time))) (let ((.def_2 (<= F_71_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (not .def_3))) (let ((.def_5 (F F_71_time))) (let ((.def_6 (not .def_5))) (let ((.def_7 (or .def_6 .def_4))) .def_7)))))))))))(let ((.def_1 (= H_61_time t_Measure_306_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_306_time t_Measure_306_ba t_Measure_306_na t_Measure_306_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H H_61_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_52 (forall ((H_60_time Int)) (let ((.def_0 (exists ((t_Measure_305_time Int)(t_Measure_305_ba Bool)(t_Measure_305_na Int)(t_Measure_305_bb Bool)) (let ((.def_0 (exists ((t_F_41_time Int)) (let ((.def_0 (+ H_60_time 0))) (let ((.def_1 (<= .def_0 t_F_41_time))) (let ((.def_2 (+ H_60_time 10))) (let ((.def_3 (<= t_F_41_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (F t_F_41_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= H_60_time t_Measure_305_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_305_time t_Measure_305_ba t_Measure_305_na t_Measure_305_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H H_60_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_53 (forall ((F_70_time Int)) (let ((.def_0 (exists ((t_Measure_304_time Int)(t_Measure_304_ba Bool)(t_Measure_304_na Int)(t_Measure_304_bb Bool)) (let ((.def_0 (exists ((t_G_84_time Int)) (let ((.def_0 (+ F_70_time 0))) (let ((.def_1 (<= .def_0 t_G_84_time))) (let ((.def_2 (+ F_70_time 5))) (let ((.def_3 (<= t_G_84_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_84_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_304_bb))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (exists ((t_H_30_time Int)) (let ((.def_0 (+ F_70_time 0))) (let ((.def_1 (<= .def_0 t_H_30_time))) (let ((.def_2 (+ F_70_time 10))) (let ((.def_3 (<= t_H_30_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (H t_H_30_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_6 (not t_Measure_304_bb))) (let ((.def_7 (or .def_1 .def_6))) (let ((.def_8 (or .def_7 .def_5))) (let ((.def_9 (and .def_8 .def_4))) (let ((.def_10 (= F_70_time t_Measure_304_time))) (let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (Measure t_Measure_304_time t_Measure_304_ba t_Measure_304_na t_Measure_304_bb))) (let ((.def_13 (and .def_12 .def_11))) .def_13)))))))))))))))))(let ((.def_1 (F F_70_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_54 (forall ((E_83_time Int)) (let ((.def_0 (exists ((t_Measure_303_time Int)(t_Measure_303_ba Bool)(t_Measure_303_na Int)(t_Measure_303_bb Bool)) (let ((.def_0 (exists ((t_G_83_time Int)) (let ((.def_0 (+ E_83_time 0))) (let ((.def_1 (<= .def_0 t_G_83_time))) (let ((.def_2 (+ E_83_time 10))) (let ((.def_3 (<= t_G_83_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_83_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 1 t_Measure_303_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_83_time Int)) (let ((.def_0 (+ E_83_time 0))) (let ((.def_1 (<= .def_0 G_83_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_83_time 10))) (let ((.def_4 (<= G_83_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_83_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_303_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_83_time t_Measure_303_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_303_time t_Measure_303_ba t_Measure_303_na t_Measure_303_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_83_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_55 (forall ((E_82_time Int)) (let ((.def_0 (exists ((t_Measure_302_time Int)(t_Measure_302_ba Bool)(t_Measure_302_na Int)(t_Measure_302_bb Bool)) (let ((.def_0 (exists ((t_G_82_time Int)) (let ((.def_0 (+ E_82_time 0))) (let ((.def_1 (<= .def_0 t_G_82_time))) (let ((.def_2 (+ E_82_time 10))) (let ((.def_3 (<= t_G_82_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_82_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 3 t_Measure_302_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_82_time Int)) (let ((.def_0 (+ E_82_time 0))) (let ((.def_1 (<= .def_0 G_82_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_82_time 10))) (let ((.def_4 (<= G_82_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_82_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_302_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_82_time t_Measure_302_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_302_time t_Measure_302_ba t_Measure_302_na t_Measure_302_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_82_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_56 (forall ((E_81_time Int)) (let ((.def_0 (exists ((t_Measure_301_time Int)(t_Measure_301_ba Bool)(t_Measure_301_na Int)(t_Measure_301_bb Bool)) (let ((.def_0 (exists ((t_G_81_time Int)) (let ((.def_0 (+ E_81_time 0))) (let ((.def_1 (<= .def_0 t_G_81_time))) (let ((.def_2 (+ E_81_time 10))) (let ((.def_3 (<= t_G_81_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_81_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_301_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_81_time Int)) (let ((.def_0 (+ E_81_time 0))) (let ((.def_1 (<= .def_0 G_81_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_81_time 10))) (let ((.def_4 (<= G_81_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_81_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_301_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_81_time t_Measure_301_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_301_time t_Measure_301_ba t_Measure_301_na t_Measure_301_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_81_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_57 (forall ((E_80_time Int)) (let ((.def_0 (exists ((t_Measure_300_time Int)(t_Measure_300_ba Bool)(t_Measure_300_na Int)(t_Measure_300_bb Bool)) (let ((.def_0 (exists ((t_F_40_time Int)) (let ((.def_0 (+ E_80_time 0))) (let ((.def_1 (<= .def_0 t_F_40_time))) (let ((.def_2 (+ E_80_time 5))) (let ((.def_3 (<= t_F_40_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (F t_F_40_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_300_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 t_Measure_300_ba))) (let ((.def_5 (or .def_4 .def_1))) (let ((.def_6 (or .def_5 .def_0))) (let ((.def_7 (exists ((t_G_80_time Int)) (let ((.def_0 (+ E_80_time 0))) (let ((.def_1 (<= .def_0 t_G_80_time))) (let ((.def_2 (+ E_80_time 10))) (let ((.def_3 (<= t_G_80_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_80_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_8 (not t_Measure_300_ba))) (let ((.def_9 (or .def_3 .def_8))) (let ((.def_10 (or .def_9 .def_7))) (let ((.def_11 (forall ((G_80_time Int)) (let ((.def_0 (+ E_80_time 0))) (let ((.def_1 (<= .def_0 G_80_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_80_time 20))) (let ((.def_4 (<= G_80_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_80_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_12 (not .def_2))) (let ((.def_13 (or .def_1 .def_12))) (let ((.def_14 (or .def_13 .def_11))) (let ((.def_15 (and .def_14 .def_10 .def_6))) (let ((.def_16 (= E_80_time t_Measure_300_time))) (let ((.def_17 (and .def_16 .def_15))) (let ((.def_18 (Measure t_Measure_300_time t_Measure_300_ba t_Measure_300_na t_Measure_300_bb))) (let ((.def_19 (and .def_18 .def_17))) .def_19)))))))))))))))))))))))(let ((.def_1 (E E_80_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_58 (forall ((C_114_time Int)) (let ((.def_0 (exists ((t_Measure_297_time Int)(t_Measure_297_ba Bool)(t_Measure_297_na Int)(t_Measure_297_bb Bool)) (let ((.def_0 (exists ((t_Measure_298_time Int)(t_Measure_298_ba Bool)(t_Measure_298_na Int)(t_Measure_298_bb Bool)) (let ((.def_0 (exists ((t_Measure_299_time Int)(t_Measure_299_ba Bool)(t_Measure_299_na Int)(t_Measure_299_bb Bool)) (let ((.def_0 (exists ((t_D_152_time Int)) (let ((.def_0 (+ t_Measure_299_time 0))) (let ((.def_1 (<= .def_0 t_D_152_time))) (let ((.def_2 (+ t_Measure_299_time 10))) (let ((.def_3 (<= t_D_152_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_152_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (exists ((t_E_41_time Int)) (let ((.def_0 (+ t_Measure_299_time 0))) (let ((.def_1 (<= .def_0 t_E_41_time))) (let ((.def_2 (<= t_E_41_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (E t_E_41_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_298_time 40))) (let ((.def_4 (= .def_3 t_Measure_299_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_299_time t_Measure_299_ba t_Measure_299_na t_Measure_299_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_151_time Int)) (let ((.def_0 (+ t_Measure_298_time 0))) (let ((.def_1 (<= .def_0 t_D_151_time))) (let ((.def_2 (+ t_Measure_298_time 40))) (let ((.def_3 (<= t_D_151_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_151_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_297_time 250))) (let ((.def_4 (= .def_3 t_Measure_298_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_298_time t_Measure_298_ba t_Measure_298_na t_Measure_298_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_150_time Int)) (let ((.def_0 (+ C_114_time 0))) (let ((.def_1 (<= .def_0 t_D_150_time))) (let ((.def_2 (+ C_114_time 250))) (let ((.def_3 (<= t_D_150_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_150_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_114_time t_Measure_297_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_297_time t_Measure_297_ba t_Measure_297_na t_Measure_297_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_114_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_59 (forall ((C_113_time Int)) (let ((.def_0 (exists ((t_Measure_296_time Int)(t_Measure_296_ba Bool)(t_Measure_296_na Int)(t_Measure_296_bb Bool)) (let ((.def_0 (exists ((t_E_40_time Int)) (let ((.def_0 (+ C_113_time 0))) (let ((.def_1 (<= .def_0 t_E_40_time))) (let ((.def_2 (+ C_113_time 250))) (let ((.def_3 (<= t_E_40_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (E t_E_40_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_113_time t_Measure_296_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_296_time t_Measure_296_ba t_Measure_296_na t_Measure_296_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_113_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_60 (forall ((C_112_time Int)) (let ((.def_0 (exists ((t_Measure_293_time Int)(t_Measure_293_ba Bool)(t_Measure_293_na Int)(t_Measure_293_bb Bool)) (let ((.def_0 (exists ((t_Measure_294_time Int)(t_Measure_294_ba Bool)(t_Measure_294_na Int)(t_Measure_294_bb Bool)) (let ((.def_0 (exists ((t_Measure_295_time Int)(t_Measure_295_ba Bool)(t_Measure_295_na Int)(t_Measure_295_bb Bool)) (let ((.def_0 (exists ((t_D_149_time Int)) (let ((.def_0 (+ t_Measure_295_time 0))) (let ((.def_1 (<= .def_0 t_D_149_time))) (let ((.def_2 (+ t_Measure_295_time 10))) (let ((.def_3 (<= t_D_149_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_149_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_294_time 40))) (let ((.def_2 (= .def_1 t_Measure_295_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_295_time t_Measure_295_ba t_Measure_295_na t_Measure_295_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_148_time Int)) (let ((.def_0 (+ t_Measure_294_time 0))) (let ((.def_1 (<= .def_0 t_D_148_time))) (let ((.def_2 (+ t_Measure_294_time 40))) (let ((.def_3 (<= t_D_148_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_148_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_293_time 250))) (let ((.def_4 (= .def_3 t_Measure_294_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_294_time t_Measure_294_ba t_Measure_294_na t_Measure_294_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_147_time Int)) (let ((.def_0 (+ C_112_time 0))) (let ((.def_1 (<= .def_0 t_D_147_time))) (let ((.def_2 (+ C_112_time 250))) (let ((.def_3 (<= t_D_147_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_147_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_112_time t_Measure_293_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_293_time t_Measure_293_ba t_Measure_293_na t_Measure_293_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_112_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_61 (forall ((C_111_time Int)) (let ((.def_0 (exists ((t_Measure_291_time Int)(t_Measure_291_ba Bool)(t_Measure_291_na Int)(t_Measure_291_bb Bool)) (let ((.def_0 (exists ((t_Measure_292_time Int)(t_Measure_292_ba Bool)(t_Measure_292_na Int)(t_Measure_292_bb Bool)) (let ((.def_0 (exists ((t_D_146_time Int)) (let ((.def_0 (+ t_Measure_292_time 0))) (let ((.def_1 (<= .def_0 t_D_146_time))) (let ((.def_2 (+ t_Measure_292_time 51))) (let ((.def_3 (<= t_D_146_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_146_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_291_time 250))) (let ((.def_2 (= .def_1 t_Measure_292_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_292_time t_Measure_292_ba t_Measure_292_na t_Measure_292_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_145_time Int)) (let ((.def_0 (+ C_111_time 0))) (let ((.def_1 (<= .def_0 t_D_145_time))) (let ((.def_2 (+ C_111_time 250))) (let ((.def_3 (<= t_D_145_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_145_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_111_time t_Measure_291_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_291_time t_Measure_291_ba t_Measure_291_na t_Measure_291_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_111_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_62 (forall ((C_110_time Int)) (let ((.def_0 (exists ((t_Measure_290_time Int)(t_Measure_290_ba Bool)(t_Measure_290_na Int)(t_Measure_290_bb Bool)) (let ((.def_0 (exists ((t_D_144_time Int)) (let ((.def_0 (+ C_110_time 0))) (let ((.def_1 (<= .def_0 t_D_144_time))) (let ((.def_2 (+ C_110_time 301))) (let ((.def_3 (<= t_D_144_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_144_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_110_time t_Measure_290_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_290_time t_Measure_290_ba t_Measure_290_na t_Measure_290_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_110_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_63 (forall ((C_109_time Int)) (let ((.def_0 (exists ((t_Measure_289_time Int)(t_Measure_289_ba Bool)(t_Measure_289_na Int)(t_Measure_289_bb Bool)) (let ((.def_0 (exists ((t_D_143_time Int)) (let ((.def_0 (+ C_109_time 0))) (let ((.def_1 (<= .def_0 t_D_143_time))) (let ((.def_2 (+ C_109_time 300))) (let ((.def_3 (<= t_D_143_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_143_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_109_time t_Measure_289_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_289_time t_Measure_289_ba t_Measure_289_na t_Measure_289_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_109_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_64 (forall ((A_79_time Int)) (let ((.def_0 (exists ((t_Measure_288_time Int)(t_Measure_288_ba Bool)(t_Measure_288_na Int)(t_Measure_288_bb Bool)) (let ((.def_0 (exists ((t_C_54_time Int)) (let ((.def_0 (+ A_79_time 0))) (let ((.def_1 (<= .def_0 t_C_54_time))) (let ((.def_2 (<= t_C_54_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_54_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_288_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= A_79_time t_Measure_288_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_288_time t_Measure_288_ba t_Measure_288_na t_Measure_288_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (A A_79_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_65 (forall ((B_62_time Int)) (let ((.def_0 (exists ((t_Measure_287_time Int)(t_Measure_287_ba Bool)(t_Measure_287_na Int)(t_Measure_287_bb Bool)) (let ((.def_0 (exists ((t_C_53_time Int)) (let ((.def_0 (+ B_62_time 0))) (let ((.def_1 (<= .def_0 t_C_53_time))) (let ((.def_2 (<= t_C_53_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_53_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 100 t_Measure_287_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_62_time t_Measure_287_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_287_time t_Measure_287_ba t_Measure_287_na t_Measure_287_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_62_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_66 (forall ((B_61_time Int)) (let ((.def_0 (exists ((t_Measure_286_time Int)(t_Measure_286_ba Bool)(t_Measure_286_na Int)(t_Measure_286_bb Bool)) (let ((.def_0 (exists ((t_C_52_time Int)) (let ((.def_0 (+ B_61_time 0))) (let ((.def_1 (<= .def_0 t_C_52_time))) (let ((.def_2 (<= t_C_52_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_52_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_286_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_61_time t_Measure_286_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_286_time t_Measure_286_ba t_Measure_286_na t_Measure_286_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_61_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_67 (forall ((A_78_time Int)) (let ((.def_0 (exists ((t_Measure_285_time Int)(t_Measure_285_ba Bool)(t_Measure_285_na Int)(t_Measure_285_bb Bool)) (let ((.def_0 (exists ((t_B_51_time Int)) (let ((.def_0 (+ A_78_time 0))) (let ((.def_1 (<= .def_0 t_B_51_time))) (let ((.def_2 (<= t_B_51_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_51_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_285_ba))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (and true .def_4))) (let ((.def_6 (= A_78_time t_Measure_285_time))) (let ((.def_7 (and .def_6 .def_5))) (let ((.def_8 (Measure t_Measure_285_time t_Measure_285_ba t_Measure_285_na t_Measure_285_bb))) (let ((.def_9 (and .def_8 .def_7))) .def_9)))))))))))))(let ((.def_1 (A A_78_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_68 (forall ((A_77_time Int)) (let ((.def_0 (exists ((t_Measure_284_time Int)(t_Measure_284_ba Bool)(t_Measure_284_na Int)(t_Measure_284_bb Bool)) (let ((.def_0 (exists ((t_B_50_time Int)) (let ((.def_0 (+ A_77_time 0))) (let ((.def_1 (<= .def_0 t_B_50_time))) (let ((.def_2 (<= t_B_50_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_50_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not t_Measure_284_ba))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= A_77_time t_Measure_284_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_284_time t_Measure_284_ba t_Measure_284_na t_Measure_284_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (A A_77_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_69 (forall ((A_76_time Int)) (let ((.def_0 (exists ((t_Measure_283_time Int)(t_Measure_283_ba Bool)(t_Measure_283_na Int)(t_Measure_283_bb Bool)) (let ((.def_0 (exists ((t_B_49_time Int)) (let ((.def_0 (+ A_76_time 0))) (let ((.def_1 (<= .def_0 t_B_49_time))) (let ((.def_2 (<= t_B_49_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_49_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (= A_76_time t_Measure_283_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_283_time t_Measure_283_ba t_Measure_283_na t_Measure_283_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_76_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_70 (exists ((t_C_51_time Int)) (let ((.def_0 (exists ((t_Measure_280_time Int)(t_Measure_280_ba Bool)(t_Measure_280_na Int)(t_Measure_280_bb Bool)) (let ((.def_0 (exists ((t_Measure_281_time Int)(t_Measure_281_ba Bool)(t_Measure_281_na Int)(t_Measure_281_bb Bool)) (let ((.def_0 (exists ((t_Measure_282_time Int)(t_Measure_282_ba Bool)(t_Measure_282_na Int)(t_Measure_282_bb Bool)) (let ((.def_0 (forall ((D_49_time Int)) (let ((.def_0 (+ t_Measure_282_time 0))) (let ((.def_1 (<= .def_0 D_49_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_Measure_282_time 10))) (let ((.def_4 (<= D_49_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (D D_49_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (not t_Measure_282_ba))) (let ((.def_2 (and true .def_1))) (let ((.def_3 (and .def_2 true))) (let ((.def_4 (and .def_3 .def_0))) (let ((.def_5 (not true))) (let ((.def_6 (or .def_5 .def_4))) (let ((.def_7 (+ t_Measure_281_time 40))) (let ((.def_8 (= .def_7 t_Measure_282_time))) (let ((.def_9 (and .def_8 .def_6))) (let ((.def_10 (Measure t_Measure_282_time t_Measure_282_ba t_Measure_282_na t_Measure_282_bb))) (let ((.def_11 (and .def_10 .def_9))) .def_11)))))))))))))))(let ((.def_1 (forall ((D_48_time Int)) (let ((.def_0 (+ t_Measure_281_time 0))) (let ((.def_1 (<= .def_0 D_48_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_Measure_281_time 40))) (let ((.def_4 (<= D_48_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (D D_48_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (+ t_Measure_280_time 250))) (let ((.def_4 (= .def_3 t_Measure_281_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_281_time t_Measure_281_ba t_Measure_281_na t_Measure_281_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (forall ((D_47_time Int)) (let ((.def_0 (+ t_C_51_time 0))) (let ((.def_1 (<= .def_0 D_47_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_C_51_time 250))) (let ((.def_4 (<= D_47_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (D D_47_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (= t_C_51_time t_Measure_280_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_280_time t_Measure_280_ba t_Measure_280_na t_Measure_280_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C t_C_51_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_71 (and .def_70 .def_69 .def_68 .def_67 .def_66 .def_65 .def_64 .def_63 .def_62 .def_61 .def_60 .def_59 .def_58 .def_57 .def_56 .def_55 .def_54 .def_53 .def_52 .def_51 .def_50 .def_49 .def_48 .def_43 .def_38 .def_33 .def_28 .def_23 .def_18 .def_13 .def_8 .def_7 .def_6 .def_5 .def_4 .def_3 .def_2 .def_1 .def_0))) .def_71)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
