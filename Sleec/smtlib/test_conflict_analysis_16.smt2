(set-logic UFLIRA)
(declare-fun Measure_50_presence () Bool)
(declare-fun G_135_presence () Bool)
(declare-fun E_135_presence () Bool)
(declare-fun Measure_49_presence () Bool)
(declare-fun C_186_presence () Bool)
(declare-fun A (Int) Bool)
(declare-fun A_135_presence () Bool)
(declare-fun B (Int) Bool)
(declare-fun G (Int) Bool)
(declare-fun H_101_presence () Bool)
(declare-fun C (Int) Bool)
(declare-fun F_118_presence () Bool)
(declare-fun D (Int) Bool)
(declare-fun E (Int) Bool)
(declare-fun F (Int) Bool)
(declare-fun Measure_48_presence () Bool)
(declare-fun H (Int) Bool)
(declare-fun D_67_presence () Bool)
(declare-fun Measure (Int Bool Int Bool) Bool)
(declare-fun B_101_presence () Bool)
(assert (let ((.def_0 (forall ((Measure_50_time Int)(Measure_50_ba Bool)(Measure_50_na Int)(Measure_50_bb Bool)) (let ((.def_0 (<= 0 Measure_50_time))) (let ((.def_1 (and .def_0 true true true))) (let ((.def_2 (=> Measure_50_presence .def_1))) (let ((.def_3 (Measure Measure_50_time Measure_50_ba Measure_50_na Measure_50_bb))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((H_101_time Int)) (let ((.def_0 (<= 0 H_101_time))) (let ((.def_1 (=> H_101_presence .def_0))) (let ((.def_2 (H H_101_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((G_135_time Int)) (let ((.def_0 (<= 0 G_135_time))) (let ((.def_1 (=> G_135_presence .def_0))) (let ((.def_2 (G G_135_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((F_118_time Int)) (let ((.def_0 (<= 0 F_118_time))) (let ((.def_1 (=> F_118_presence .def_0))) (let ((.def_2 (F F_118_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (forall ((E_135_time Int)) (let ((.def_0 (<= 0 E_135_time))) (let ((.def_1 (=> E_135_presence .def_0))) (let ((.def_2 (E E_135_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_5 (forall ((D_67_time Int)) (let ((.def_0 (<= 0 D_67_time))) (let ((.def_1 (=> D_67_presence .def_0))) (let ((.def_2 (D D_67_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_6 (forall ((C_186_time Int)) (let ((.def_0 (<= 0 C_186_time))) (let ((.def_1 (=> C_186_presence .def_0))) (let ((.def_2 (C C_186_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_7 (forall ((B_101_time Int)) (let ((.def_0 (<= 0 B_101_time))) (let ((.def_1 (=> B_101_presence .def_0))) (let ((.def_2 (B B_101_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_8 (forall ((A_135_time Int)) (let ((.def_0 (<= 0 A_135_time))) (let ((.def_1 (=> A_135_presence .def_0))) (let ((.def_2 (A A_135_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_9 (exists ((t_H_50_time Int)) (let ((.def_0 (forall ((H_100_time Int)) (let ((.def_0 (<= H_100_time t_H_50_time))) (let ((.def_1 (H H_100_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_50_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_10 (exists ((t_H_49_time Int)) (let ((.def_0 (forall ((H_99_time Int)) (let ((.def_0 (<= t_H_49_time H_99_time))) (let ((.def_1 (H H_99_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_49_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (forall ((H_98_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (H H_98_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_13 (or .def_12 .def_11))) (let ((.def_14 (exists ((t_G_135_time Int)) (let ((.def_0 (forall ((G_134_time Int)) (let ((.def_0 (<= G_134_time t_G_135_time))) (let ((.def_1 (G G_134_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_135_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_15 (exists ((t_G_134_time Int)) (let ((.def_0 (forall ((G_133_time Int)) (let ((.def_0 (<= t_G_134_time G_133_time))) (let ((.def_1 (G G_133_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_134_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (forall ((G_132_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (G G_132_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (exists ((t_F_67_time Int)) (let ((.def_0 (forall ((F_117_time Int)) (let ((.def_0 (<= F_117_time t_F_67_time))) (let ((.def_1 (F F_117_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_67_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_20 (exists ((t_F_66_time Int)) (let ((.def_0 (forall ((F_116_time Int)) (let ((.def_0 (<= t_F_66_time F_116_time))) (let ((.def_1 (F F_116_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_66_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_21 (and .def_20 .def_19))) (let ((.def_22 (forall ((F_115_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (F F_115_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_23 (or .def_22 .def_21))) (let ((.def_24 (exists ((t_E_71_time Int)) (let ((.def_0 (forall ((E_134_time Int)) (let ((.def_0 (<= E_134_time t_E_71_time))) (let ((.def_1 (E E_134_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_71_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_25 (exists ((t_E_70_time Int)) (let ((.def_0 (forall ((E_133_time Int)) (let ((.def_0 (<= t_E_70_time E_133_time))) (let ((.def_1 (E E_133_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_70_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_26 (and .def_25 .def_24))) (let ((.def_27 (forall ((E_132_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (E E_132_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_28 (or .def_27 .def_26))) (let ((.def_29 (exists ((t_D_254_time Int)) (let ((.def_0 (forall ((D_66_time Int)) (let ((.def_0 (<= D_66_time t_D_254_time))) (let ((.def_1 (D D_66_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_254_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_30 (exists ((t_D_253_time Int)) (let ((.def_0 (forall ((D_65_time Int)) (let ((.def_0 (<= t_D_253_time D_65_time))) (let ((.def_1 (D D_65_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_253_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_31 (and .def_30 .def_29))) (let ((.def_32 (forall ((D_64_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (D D_64_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_33 (or .def_32 .def_31))) (let ((.def_34 (exists ((t_C_91_time Int)) (let ((.def_0 (forall ((C_185_time Int)) (let ((.def_0 (<= C_185_time t_C_91_time))) (let ((.def_1 (C C_185_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_91_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_35 (exists ((t_C_90_time Int)) (let ((.def_0 (forall ((C_184_time Int)) (let ((.def_0 (<= t_C_90_time C_184_time))) (let ((.def_1 (C C_184_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_90_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_36 (and .def_35 .def_34))) (let ((.def_37 (forall ((C_183_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (C C_183_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_38 (or .def_37 .def_36))) (let ((.def_39 (exists ((t_B_86_time Int)) (let ((.def_0 (forall ((B_100_time Int)) (let ((.def_0 (<= B_100_time t_B_86_time))) (let ((.def_1 (B B_100_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_86_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_40 (exists ((t_B_85_time Int)) (let ((.def_0 (forall ((B_99_time Int)) (let ((.def_0 (<= t_B_85_time B_99_time))) (let ((.def_1 (B B_99_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_85_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_41 (and .def_40 .def_39))) (let ((.def_42 (forall ((B_98_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (B B_98_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_43 (or .def_42 .def_41))) (let ((.def_44 (exists ((t_A_37_time Int)) (let ((.def_0 (forall ((A_134_time Int)) (let ((.def_0 (<= A_134_time t_A_37_time))) (let ((.def_1 (A A_134_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_37_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_45 (exists ((t_A_36_time Int)) (let ((.def_0 (forall ((A_133_time Int)) (let ((.def_0 (<= t_A_36_time A_133_time))) (let ((.def_1 (A A_133_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_36_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_46 (and .def_45 .def_44))) (let ((.def_47 (forall ((A_132_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (A A_132_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_48 (or .def_47 .def_46))) (let ((.def_49 (forall ((Measure_48_time Int)(Measure_48_ba Bool)(Measure_48_na Int)(Measure_48_bb Bool)) (let ((.def_0 (forall ((Measure_49_time Int)(Measure_49_ba Bool)(Measure_49_na Int)(Measure_49_bb Bool)) (let ((.def_0 (= Measure_48_presence Measure_49_presence))) (let ((.def_1 (= Measure_48_bb Measure_49_bb))) (let ((.def_2 (= Measure_48_na Measure_49_na))) (let ((.def_3 (= Measure_48_ba Measure_49_ba))) (let ((.def_4 (= Measure_48_time Measure_49_time))) (let ((.def_5 (and .def_4 .def_3 .def_2 .def_1 .def_0))) (let ((.def_6 (not .def_4))) (let ((.def_7 (or .def_6 .def_5))) (let ((.def_8 (Measure Measure_49_time Measure_49_ba Measure_49_na Measure_49_bb))) (let ((.def_9 (not .def_8))) (let ((.def_10 (or .def_9 .def_7))) .def_10))))))))))))))(let ((.def_1 (Measure Measure_48_time Measure_48_ba Measure_48_na Measure_48_bb))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_50 (forall ((F_114_time Int)) (let ((.def_0 (exists ((t_Measure_492_time Int)(t_Measure_492_ba Bool)(t_Measure_492_na Int)(t_Measure_492_bb Bool)) (let ((.def_0 (exists ((t_G_133_time Int)) (let ((.def_0 (<= F_114_time t_G_133_time))) (let ((.def_1 (G t_G_133_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (= F_114_time t_Measure_492_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_492_time t_Measure_492_ba t_Measure_492_na t_Measure_492_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (F F_114_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_51 (forall ((H_97_time Int)) (let ((.def_0 (exists ((t_Measure_491_time Int)(t_Measure_491_ba Bool)(t_Measure_491_na Int)(t_Measure_491_bb Bool)) (let ((.def_0 (forall ((F_113_time Int)) (let ((.def_0 (+ H_97_time 0))) (let ((.def_1 (<= .def_0 F_113_time))) (let ((.def_2 (<= F_113_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (not .def_3))) (let ((.def_5 (F F_113_time))) (let ((.def_6 (not .def_5))) (let ((.def_7 (or .def_6 .def_4))) .def_7)))))))))))(let ((.def_1 (= H_97_time t_Measure_491_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_491_time t_Measure_491_ba t_Measure_491_na t_Measure_491_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H H_97_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_52 (forall ((H_96_time Int)) (let ((.def_0 (exists ((t_Measure_490_time Int)(t_Measure_490_ba Bool)(t_Measure_490_na Int)(t_Measure_490_bb Bool)) (let ((.def_0 (exists ((t_F_65_time Int)) (let ((.def_0 (+ H_96_time 0))) (let ((.def_1 (<= .def_0 t_F_65_time))) (let ((.def_2 (+ H_96_time 10))) (let ((.def_3 (<= t_F_65_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (F t_F_65_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= H_96_time t_Measure_490_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_490_time t_Measure_490_ba t_Measure_490_na t_Measure_490_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H H_96_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_53 (forall ((F_112_time Int)) (let ((.def_0 (exists ((t_Measure_489_time Int)(t_Measure_489_ba Bool)(t_Measure_489_na Int)(t_Measure_489_bb Bool)) (let ((.def_0 (exists ((t_G_132_time Int)) (let ((.def_0 (+ F_112_time 0))) (let ((.def_1 (<= .def_0 t_G_132_time))) (let ((.def_2 (+ F_112_time 5))) (let ((.def_3 (<= t_G_132_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_132_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_489_bb))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (exists ((t_H_48_time Int)) (let ((.def_0 (+ F_112_time 0))) (let ((.def_1 (<= .def_0 t_H_48_time))) (let ((.def_2 (+ F_112_time 10))) (let ((.def_3 (<= t_H_48_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (H t_H_48_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_6 (not t_Measure_489_bb))) (let ((.def_7 (or .def_1 .def_6))) (let ((.def_8 (or .def_7 .def_5))) (let ((.def_9 (and .def_8 .def_4))) (let ((.def_10 (= F_112_time t_Measure_489_time))) (let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (Measure t_Measure_489_time t_Measure_489_ba t_Measure_489_na t_Measure_489_bb))) (let ((.def_13 (and .def_12 .def_11))) .def_13)))))))))))))))))(let ((.def_1 (F F_112_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_54 (forall ((E_131_time Int)) (let ((.def_0 (exists ((t_Measure_488_time Int)(t_Measure_488_ba Bool)(t_Measure_488_na Int)(t_Measure_488_bb Bool)) (let ((.def_0 (exists ((t_G_131_time Int)) (let ((.def_0 (+ E_131_time 0))) (let ((.def_1 (<= .def_0 t_G_131_time))) (let ((.def_2 (+ E_131_time 10))) (let ((.def_3 (<= t_G_131_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_131_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 1 t_Measure_488_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_131_time Int)) (let ((.def_0 (+ E_131_time 0))) (let ((.def_1 (<= .def_0 G_131_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_131_time 10))) (let ((.def_4 (<= G_131_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_131_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_488_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_131_time t_Measure_488_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_488_time t_Measure_488_ba t_Measure_488_na t_Measure_488_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_131_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_55 (forall ((E_130_time Int)) (let ((.def_0 (exists ((t_Measure_487_time Int)(t_Measure_487_ba Bool)(t_Measure_487_na Int)(t_Measure_487_bb Bool)) (let ((.def_0 (exists ((t_G_130_time Int)) (let ((.def_0 (+ E_130_time 0))) (let ((.def_1 (<= .def_0 t_G_130_time))) (let ((.def_2 (+ E_130_time 10))) (let ((.def_3 (<= t_G_130_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_130_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 3 t_Measure_487_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_130_time Int)) (let ((.def_0 (+ E_130_time 0))) (let ((.def_1 (<= .def_0 G_130_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_130_time 10))) (let ((.def_4 (<= G_130_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_130_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_487_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_130_time t_Measure_487_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_487_time t_Measure_487_ba t_Measure_487_na t_Measure_487_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_130_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_56 (forall ((E_129_time Int)) (let ((.def_0 (exists ((t_Measure_486_time Int)(t_Measure_486_ba Bool)(t_Measure_486_na Int)(t_Measure_486_bb Bool)) (let ((.def_0 (exists ((t_G_129_time Int)) (let ((.def_0 (+ E_129_time 0))) (let ((.def_1 (<= .def_0 t_G_129_time))) (let ((.def_2 (+ E_129_time 10))) (let ((.def_3 (<= t_G_129_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_129_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_486_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_129_time Int)) (let ((.def_0 (+ E_129_time 0))) (let ((.def_1 (<= .def_0 G_129_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_129_time 10))) (let ((.def_4 (<= G_129_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_129_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_486_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_129_time t_Measure_486_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_486_time t_Measure_486_ba t_Measure_486_na t_Measure_486_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_129_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_57 (forall ((E_128_time Int)) (let ((.def_0 (exists ((t_Measure_485_time Int)(t_Measure_485_ba Bool)(t_Measure_485_na Int)(t_Measure_485_bb Bool)) (let ((.def_0 (exists ((t_F_64_time Int)) (let ((.def_0 (+ E_128_time 0))) (let ((.def_1 (<= .def_0 t_F_64_time))) (let ((.def_2 (+ E_128_time 5))) (let ((.def_3 (<= t_F_64_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (F t_F_64_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_485_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 t_Measure_485_ba))) (let ((.def_5 (or .def_4 .def_1))) (let ((.def_6 (or .def_5 .def_0))) (let ((.def_7 (exists ((t_G_128_time Int)) (let ((.def_0 (+ E_128_time 0))) (let ((.def_1 (<= .def_0 t_G_128_time))) (let ((.def_2 (+ E_128_time 10))) (let ((.def_3 (<= t_G_128_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_128_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_8 (not t_Measure_485_ba))) (let ((.def_9 (or .def_3 .def_8))) (let ((.def_10 (or .def_9 .def_7))) (let ((.def_11 (forall ((G_128_time Int)) (let ((.def_0 (+ E_128_time 0))) (let ((.def_1 (<= .def_0 G_128_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_128_time 20))) (let ((.def_4 (<= G_128_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_128_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_12 (not .def_2))) (let ((.def_13 (or .def_1 .def_12))) (let ((.def_14 (or .def_13 .def_11))) (let ((.def_15 (and .def_14 .def_10 .def_6))) (let ((.def_16 (= E_128_time t_Measure_485_time))) (let ((.def_17 (and .def_16 .def_15))) (let ((.def_18 (Measure t_Measure_485_time t_Measure_485_ba t_Measure_485_na t_Measure_485_bb))) (let ((.def_19 (and .def_18 .def_17))) .def_19)))))))))))))))))))))))(let ((.def_1 (E E_128_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_58 (forall ((C_182_time Int)) (let ((.def_0 (exists ((t_Measure_482_time Int)(t_Measure_482_ba Bool)(t_Measure_482_na Int)(t_Measure_482_bb Bool)) (let ((.def_0 (exists ((t_Measure_483_time Int)(t_Measure_483_ba Bool)(t_Measure_483_na Int)(t_Measure_483_bb Bool)) (let ((.def_0 (exists ((t_Measure_484_time Int)(t_Measure_484_ba Bool)(t_Measure_484_na Int)(t_Measure_484_bb Bool)) (let ((.def_0 (exists ((t_D_252_time Int)) (let ((.def_0 (+ t_Measure_484_time 0))) (let ((.def_1 (<= .def_0 t_D_252_time))) (let ((.def_2 (+ t_Measure_484_time 10))) (let ((.def_3 (<= t_D_252_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_252_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (exists ((t_E_69_time Int)) (let ((.def_0 (+ t_Measure_484_time 0))) (let ((.def_1 (<= .def_0 t_E_69_time))) (let ((.def_2 (<= t_E_69_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (E t_E_69_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_483_time 40))) (let ((.def_4 (= .def_3 t_Measure_484_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_484_time t_Measure_484_ba t_Measure_484_na t_Measure_484_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_251_time Int)) (let ((.def_0 (+ t_Measure_483_time 0))) (let ((.def_1 (<= .def_0 t_D_251_time))) (let ((.def_2 (+ t_Measure_483_time 40))) (let ((.def_3 (<= t_D_251_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_251_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_482_time 250))) (let ((.def_4 (= .def_3 t_Measure_483_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_483_time t_Measure_483_ba t_Measure_483_na t_Measure_483_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_250_time Int)) (let ((.def_0 (+ C_182_time 0))) (let ((.def_1 (<= .def_0 t_D_250_time))) (let ((.def_2 (+ C_182_time 250))) (let ((.def_3 (<= t_D_250_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_250_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_182_time t_Measure_482_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_482_time t_Measure_482_ba t_Measure_482_na t_Measure_482_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_182_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_59 (forall ((C_181_time Int)) (let ((.def_0 (exists ((t_Measure_481_time Int)(t_Measure_481_ba Bool)(t_Measure_481_na Int)(t_Measure_481_bb Bool)) (let ((.def_0 (exists ((t_E_68_time Int)) (let ((.def_0 (+ C_181_time 0))) (let ((.def_1 (<= .def_0 t_E_68_time))) (let ((.def_2 (+ C_181_time 250))) (let ((.def_3 (<= t_E_68_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (E t_E_68_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_181_time t_Measure_481_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_481_time t_Measure_481_ba t_Measure_481_na t_Measure_481_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_181_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_60 (forall ((C_180_time Int)) (let ((.def_0 (exists ((t_Measure_478_time Int)(t_Measure_478_ba Bool)(t_Measure_478_na Int)(t_Measure_478_bb Bool)) (let ((.def_0 (exists ((t_Measure_479_time Int)(t_Measure_479_ba Bool)(t_Measure_479_na Int)(t_Measure_479_bb Bool)) (let ((.def_0 (exists ((t_Measure_480_time Int)(t_Measure_480_ba Bool)(t_Measure_480_na Int)(t_Measure_480_bb Bool)) (let ((.def_0 (exists ((t_D_249_time Int)) (let ((.def_0 (+ t_Measure_480_time 0))) (let ((.def_1 (<= .def_0 t_D_249_time))) (let ((.def_2 (+ t_Measure_480_time 10))) (let ((.def_3 (<= t_D_249_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_249_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_480_ba))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (and true .def_4))) (let ((.def_6 (+ t_Measure_479_time 40))) (let ((.def_7 (= .def_6 t_Measure_480_time))) (let ((.def_8 (and .def_7 .def_5))) (let ((.def_9 (Measure t_Measure_480_time t_Measure_480_ba t_Measure_480_na t_Measure_480_bb))) (let ((.def_10 (and .def_9 .def_8))) .def_10))))))))))))))(let ((.def_1 (exists ((t_D_248_time Int)) (let ((.def_0 (+ t_Measure_479_time 0))) (let ((.def_1 (<= .def_0 t_D_248_time))) (let ((.def_2 (+ t_Measure_479_time 40))) (let ((.def_3 (<= t_D_248_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_248_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_478_time 250))) (let ((.def_4 (= .def_3 t_Measure_479_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_479_time t_Measure_479_ba t_Measure_479_na t_Measure_479_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_247_time Int)) (let ((.def_0 (+ C_180_time 0))) (let ((.def_1 (<= .def_0 t_D_247_time))) (let ((.def_2 (+ C_180_time 250))) (let ((.def_3 (<= t_D_247_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_247_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_180_time t_Measure_478_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_478_time t_Measure_478_ba t_Measure_478_na t_Measure_478_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_180_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_61 (forall ((C_179_time Int)) (let ((.def_0 (exists ((t_Measure_475_time Int)(t_Measure_475_ba Bool)(t_Measure_475_na Int)(t_Measure_475_bb Bool)) (let ((.def_0 (exists ((t_Measure_476_time Int)(t_Measure_476_ba Bool)(t_Measure_476_na Int)(t_Measure_476_bb Bool)) (let ((.def_0 (exists ((t_Measure_477_time Int)(t_Measure_477_ba Bool)(t_Measure_477_na Int)(t_Measure_477_bb Bool)) (let ((.def_0 (exists ((t_D_246_time Int)) (let ((.def_0 (+ t_Measure_477_time 0))) (let ((.def_1 (<= .def_0 t_D_246_time))) (let ((.def_2 (+ t_Measure_477_time 10))) (let ((.def_3 (<= t_D_246_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_246_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_476_time 40))) (let ((.def_2 (= .def_1 t_Measure_477_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_477_time t_Measure_477_ba t_Measure_477_na t_Measure_477_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_245_time Int)) (let ((.def_0 (+ t_Measure_476_time 0))) (let ((.def_1 (<= .def_0 t_D_245_time))) (let ((.def_2 (+ t_Measure_476_time 40))) (let ((.def_3 (<= t_D_245_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_245_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_475_time 250))) (let ((.def_4 (= .def_3 t_Measure_476_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_476_time t_Measure_476_ba t_Measure_476_na t_Measure_476_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_244_time Int)) (let ((.def_0 (+ C_179_time 0))) (let ((.def_1 (<= .def_0 t_D_244_time))) (let ((.def_2 (+ C_179_time 250))) (let ((.def_3 (<= t_D_244_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_244_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_179_time t_Measure_475_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_475_time t_Measure_475_ba t_Measure_475_na t_Measure_475_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_179_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_62 (forall ((C_178_time Int)) (let ((.def_0 (exists ((t_Measure_473_time Int)(t_Measure_473_ba Bool)(t_Measure_473_na Int)(t_Measure_473_bb Bool)) (let ((.def_0 (exists ((t_Measure_474_time Int)(t_Measure_474_ba Bool)(t_Measure_474_na Int)(t_Measure_474_bb Bool)) (let ((.def_0 (exists ((t_D_243_time Int)) (let ((.def_0 (+ t_Measure_474_time 0))) (let ((.def_1 (<= .def_0 t_D_243_time))) (let ((.def_2 (+ t_Measure_474_time 51))) (let ((.def_3 (<= t_D_243_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_243_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_473_time 250))) (let ((.def_2 (= .def_1 t_Measure_474_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_474_time t_Measure_474_ba t_Measure_474_na t_Measure_474_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_242_time Int)) (let ((.def_0 (+ C_178_time 0))) (let ((.def_1 (<= .def_0 t_D_242_time))) (let ((.def_2 (+ C_178_time 250))) (let ((.def_3 (<= t_D_242_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_242_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_178_time t_Measure_473_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_473_time t_Measure_473_ba t_Measure_473_na t_Measure_473_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_178_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_63 (forall ((C_177_time Int)) (let ((.def_0 (exists ((t_Measure_472_time Int)(t_Measure_472_ba Bool)(t_Measure_472_na Int)(t_Measure_472_bb Bool)) (let ((.def_0 (exists ((t_D_241_time Int)) (let ((.def_0 (+ C_177_time 0))) (let ((.def_1 (<= .def_0 t_D_241_time))) (let ((.def_2 (+ C_177_time 301))) (let ((.def_3 (<= t_D_241_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_241_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_177_time t_Measure_472_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_472_time t_Measure_472_ba t_Measure_472_na t_Measure_472_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_177_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_64 (forall ((C_176_time Int)) (let ((.def_0 (exists ((t_Measure_471_time Int)(t_Measure_471_ba Bool)(t_Measure_471_na Int)(t_Measure_471_bb Bool)) (let ((.def_0 (exists ((t_D_240_time Int)) (let ((.def_0 (+ C_176_time 0))) (let ((.def_1 (<= .def_0 t_D_240_time))) (let ((.def_2 (+ C_176_time 300))) (let ((.def_3 (<= t_D_240_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_240_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_176_time t_Measure_471_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_471_time t_Measure_471_ba t_Measure_471_na t_Measure_471_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_176_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_65 (forall ((A_131_time Int)) (let ((.def_0 (exists ((t_Measure_470_time Int)(t_Measure_470_ba Bool)(t_Measure_470_na Int)(t_Measure_470_bb Bool)) (let ((.def_0 (exists ((t_C_89_time Int)) (let ((.def_0 (+ A_131_time 0))) (let ((.def_1 (<= .def_0 t_C_89_time))) (let ((.def_2 (<= t_C_89_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_89_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_470_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= A_131_time t_Measure_470_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_470_time t_Measure_470_ba t_Measure_470_na t_Measure_470_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (A A_131_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_66 (forall ((B_97_time Int)) (let ((.def_0 (exists ((t_Measure_469_time Int)(t_Measure_469_ba Bool)(t_Measure_469_na Int)(t_Measure_469_bb Bool)) (let ((.def_0 (exists ((t_C_88_time Int)) (let ((.def_0 (+ B_97_time 0))) (let ((.def_1 (<= .def_0 t_C_88_time))) (let ((.def_2 (<= t_C_88_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_88_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 100 t_Measure_469_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_97_time t_Measure_469_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_469_time t_Measure_469_ba t_Measure_469_na t_Measure_469_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_97_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_67 (forall ((B_96_time Int)) (let ((.def_0 (exists ((t_Measure_468_time Int)(t_Measure_468_ba Bool)(t_Measure_468_na Int)(t_Measure_468_bb Bool)) (let ((.def_0 (exists ((t_C_87_time Int)) (let ((.def_0 (+ B_96_time 0))) (let ((.def_1 (<= .def_0 t_C_87_time))) (let ((.def_2 (<= t_C_87_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_87_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_468_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_96_time t_Measure_468_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_468_time t_Measure_468_ba t_Measure_468_na t_Measure_468_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_96_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_68 (forall ((A_130_time Int)) (let ((.def_0 (exists ((t_Measure_467_time Int)(t_Measure_467_ba Bool)(t_Measure_467_na Int)(t_Measure_467_bb Bool)) (let ((.def_0 (exists ((t_B_84_time Int)) (let ((.def_0 (+ A_130_time 0))) (let ((.def_1 (<= .def_0 t_B_84_time))) (let ((.def_2 (<= t_B_84_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_84_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_467_ba))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (and true .def_4))) (let ((.def_6 (= A_130_time t_Measure_467_time))) (let ((.def_7 (and .def_6 .def_5))) (let ((.def_8 (Measure t_Measure_467_time t_Measure_467_ba t_Measure_467_na t_Measure_467_bb))) (let ((.def_9 (and .def_8 .def_7))) .def_9)))))))))))))(let ((.def_1 (A A_130_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_69 (forall ((A_129_time Int)) (let ((.def_0 (exists ((t_Measure_466_time Int)(t_Measure_466_ba Bool)(t_Measure_466_na Int)(t_Measure_466_bb Bool)) (let ((.def_0 (exists ((t_B_83_time Int)) (let ((.def_0 (+ A_129_time 0))) (let ((.def_1 (<= .def_0 t_B_83_time))) (let ((.def_2 (<= t_B_83_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_83_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not t_Measure_466_ba))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= A_129_time t_Measure_466_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_466_time t_Measure_466_ba t_Measure_466_na t_Measure_466_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (A A_129_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_70 (forall ((A_128_time Int)) (let ((.def_0 (exists ((t_Measure_465_time Int)(t_Measure_465_ba Bool)(t_Measure_465_na Int)(t_Measure_465_bb Bool)) (let ((.def_0 (exists ((t_B_82_time Int)) (let ((.def_0 (+ A_128_time 0))) (let ((.def_1 (<= .def_0 t_B_82_time))) (let ((.def_2 (<= t_B_82_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_82_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (= A_128_time t_Measure_465_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_465_time t_Measure_465_ba t_Measure_465_na t_Measure_465_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_128_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_71 (exists ((t_E_67_time Int)) (let ((.def_0 (exists ((t_Measure_464_time Int)(t_Measure_464_ba Bool)(t_Measure_464_na Int)(t_Measure_464_bb Bool)) (let ((.def_0 (= t_E_67_time t_Measure_464_time))) (let ((.def_1 (and .def_0 t_Measure_464_ba))) (let ((.def_2 (Measure t_Measure_464_time t_Measure_464_ba t_Measure_464_na t_Measure_464_bb))) (let ((.def_3 (and .def_2 .def_1))) .def_3)))))))(let ((.def_1 (E t_E_67_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_72 (and .def_71 .def_70 .def_69 .def_68 .def_67 .def_66 .def_65 .def_64 .def_63 .def_62 .def_61 .def_60 .def_59 .def_58 .def_57 .def_56 .def_55 .def_54 .def_53 .def_52 .def_51 .def_50 .def_49 .def_48 .def_43 .def_38 .def_33 .def_28 .def_23 .def_18 .def_13 .def_8 .def_7 .def_6 .def_5 .def_4 .def_3 .def_2 .def_1 .def_0))) .def_72))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
