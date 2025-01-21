(set-logic UFLIRA)
(declare-fun Measure_56_presence () Bool)
(declare-fun G_152_presence () Bool)
(declare-fun E_149_presence () Bool)
(declare-fun Measure_55_presence () Bool)
(declare-fun C_204_presence () Bool)
(declare-fun A_147_presence () Bool)
(declare-fun A (Int) Bool)
(declare-fun H_113_presence () Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int) Bool)
(declare-fun F_133_presence () Bool)
(declare-fun E (Int) Bool)
(declare-fun Measure_54_presence () Bool)
(declare-fun D_88_presence () Bool)
(declare-fun F (Int) Bool)
(declare-fun H (Int) Bool)
(declare-fun G (Int) Bool)
(declare-fun B_114_presence () Bool)
(declare-fun Measure (Int Bool Int Bool) Bool)
(declare-fun D (Int) Bool)
(assert (let ((.def_0 (forall ((Measure_56_time Int)(Measure_56_ba Bool)(Measure_56_na Int)(Measure_56_bb Bool)) (let ((.def_0 (<= 0 Measure_56_time))) (let ((.def_1 (and .def_0 true true true))) (let ((.def_2 (=> Measure_56_presence .def_1))) (let ((.def_3 (Measure Measure_56_time Measure_56_ba Measure_56_na Measure_56_bb))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((H_113_time Int)) (let ((.def_0 (<= 0 H_113_time))) (let ((.def_1 (=> H_113_presence .def_0))) (let ((.def_2 (H H_113_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((G_152_time Int)) (let ((.def_0 (<= 0 G_152_time))) (let ((.def_1 (=> G_152_presence .def_0))) (let ((.def_2 (G G_152_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((F_133_time Int)) (let ((.def_0 (<= 0 F_133_time))) (let ((.def_1 (=> F_133_presence .def_0))) (let ((.def_2 (F F_133_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (forall ((E_149_time Int)) (let ((.def_0 (<= 0 E_149_time))) (let ((.def_1 (=> E_149_presence .def_0))) (let ((.def_2 (E E_149_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_5 (forall ((D_88_time Int)) (let ((.def_0 (<= 0 D_88_time))) (let ((.def_1 (=> D_88_presence .def_0))) (let ((.def_2 (D D_88_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_6 (forall ((C_204_time Int)) (let ((.def_0 (<= 0 C_204_time))) (let ((.def_1 (=> C_204_presence .def_0))) (let ((.def_2 (C C_204_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_7 (forall ((B_114_time Int)) (let ((.def_0 (<= 0 B_114_time))) (let ((.def_1 (=> B_114_presence .def_0))) (let ((.def_2 (B B_114_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_8 (forall ((A_147_time Int)) (let ((.def_0 (<= 0 A_147_time))) (let ((.def_1 (=> A_147_presence .def_0))) (let ((.def_2 (A A_147_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_9 (exists ((t_H_56_time Int)) (let ((.def_0 (forall ((H_112_time Int)) (let ((.def_0 (<= H_112_time t_H_56_time))) (let ((.def_1 (H H_112_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_56_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_10 (exists ((t_H_55_time Int)) (let ((.def_0 (forall ((H_111_time Int)) (let ((.def_0 (<= t_H_55_time H_111_time))) (let ((.def_1 (H H_111_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (H t_H_55_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (forall ((H_110_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (H H_110_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_13 (or .def_12 .def_11))) (let ((.def_14 (exists ((t_G_150_time Int)) (let ((.def_0 (forall ((G_151_time Int)) (let ((.def_0 (<= G_151_time t_G_150_time))) (let ((.def_1 (G G_151_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_150_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_15 (exists ((t_G_149_time Int)) (let ((.def_0 (forall ((G_150_time Int)) (let ((.def_0 (<= t_G_149_time G_150_time))) (let ((.def_1 (G G_150_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (G t_G_149_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (forall ((G_149_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (G G_149_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (exists ((t_F_74_time Int)) (let ((.def_0 (forall ((F_132_time Int)) (let ((.def_0 (<= F_132_time t_F_74_time))) (let ((.def_1 (F F_132_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_74_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_20 (exists ((t_F_73_time Int)) (let ((.def_0 (forall ((F_131_time Int)) (let ((.def_0 (<= t_F_73_time F_131_time))) (let ((.def_1 (F F_131_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (F t_F_73_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_21 (and .def_20 .def_19))) (let ((.def_22 (forall ((F_130_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (F F_130_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_23 (or .def_22 .def_21))) (let ((.def_24 (exists ((t_E_77_time Int)) (let ((.def_0 (forall ((E_148_time Int)) (let ((.def_0 (<= E_148_time t_E_77_time))) (let ((.def_1 (E E_148_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_77_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_25 (exists ((t_E_76_time Int)) (let ((.def_0 (forall ((E_147_time Int)) (let ((.def_0 (<= t_E_76_time E_147_time))) (let ((.def_1 (E E_147_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (E t_E_76_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_26 (and .def_25 .def_24))) (let ((.def_27 (forall ((E_146_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (E E_146_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_28 (or .def_27 .def_26))) (let ((.def_29 (exists ((t_D_271_time Int)) (let ((.def_0 (forall ((D_87_time Int)) (let ((.def_0 (<= D_87_time t_D_271_time))) (let ((.def_1 (D D_87_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_271_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_30 (exists ((t_D_270_time Int)) (let ((.def_0 (forall ((D_86_time Int)) (let ((.def_0 (<= t_D_270_time D_86_time))) (let ((.def_1 (D D_86_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (D t_D_270_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_31 (and .def_30 .def_29))) (let ((.def_32 (forall ((D_85_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (D D_85_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_33 (or .def_32 .def_31))) (let ((.def_34 (exists ((t_C_98_time Int)) (let ((.def_0 (forall ((C_203_time Int)) (let ((.def_0 (<= C_203_time t_C_98_time))) (let ((.def_1 (C C_203_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_98_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_35 (exists ((t_C_97_time Int)) (let ((.def_0 (forall ((C_202_time Int)) (let ((.def_0 (<= t_C_97_time C_202_time))) (let ((.def_1 (C C_202_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (C t_C_97_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_36 (and .def_35 .def_34))) (let ((.def_37 (forall ((C_201_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (C C_201_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_38 (or .def_37 .def_36))) (let ((.def_39 (exists ((t_B_93_time Int)) (let ((.def_0 (forall ((B_113_time Int)) (let ((.def_0 (<= B_113_time t_B_93_time))) (let ((.def_1 (B B_113_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_93_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_40 (exists ((t_B_92_time Int)) (let ((.def_0 (forall ((B_112_time Int)) (let ((.def_0 (<= t_B_92_time B_112_time))) (let ((.def_1 (B B_112_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (B t_B_92_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_41 (and .def_40 .def_39))) (let ((.def_42 (forall ((B_111_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (B B_111_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_43 (or .def_42 .def_41))) (let ((.def_44 (exists ((t_A_41_time Int)) (let ((.def_0 (forall ((A_146_time Int)) (let ((.def_0 (<= A_146_time t_A_41_time))) (let ((.def_1 (A A_146_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_41_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_45 (exists ((t_A_40_time Int)) (let ((.def_0 (forall ((A_145_time Int)) (let ((.def_0 (<= t_A_40_time A_145_time))) (let ((.def_1 (A A_145_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (A t_A_40_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_46 (and .def_45 .def_44))) (let ((.def_47 (forall ((A_144_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (A A_144_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_48 (or .def_47 .def_46))) (let ((.def_49 (forall ((Measure_54_time Int)(Measure_54_ba Bool)(Measure_54_na Int)(Measure_54_bb Bool)) (let ((.def_0 (forall ((Measure_55_time Int)(Measure_55_ba Bool)(Measure_55_na Int)(Measure_55_bb Bool)) (let ((.def_0 (= Measure_54_presence Measure_55_presence))) (let ((.def_1 (= Measure_54_bb Measure_55_bb))) (let ((.def_2 (= Measure_54_na Measure_55_na))) (let ((.def_3 (= Measure_54_ba Measure_55_ba))) (let ((.def_4 (= Measure_54_time Measure_55_time))) (let ((.def_5 (and .def_4 .def_3 .def_2 .def_1 .def_0))) (let ((.def_6 (not .def_4))) (let ((.def_7 (or .def_6 .def_5))) (let ((.def_8 (Measure Measure_55_time Measure_55_ba Measure_55_na Measure_55_bb))) (let ((.def_9 (not .def_8))) (let ((.def_10 (or .def_9 .def_7))) .def_10))))))))))))))(let ((.def_1 (Measure Measure_54_time Measure_54_ba Measure_54_na Measure_54_bb))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_50 (forall ((F_129_time Int)) (let ((.def_0 (exists ((t_Measure_531_time Int)(t_Measure_531_ba Bool)(t_Measure_531_na Int)(t_Measure_531_bb Bool)) (let ((.def_0 (exists ((t_G_148_time Int)) (let ((.def_0 (<= F_129_time t_G_148_time))) (let ((.def_1 (G t_G_148_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (= F_129_time t_Measure_531_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_531_time t_Measure_531_ba t_Measure_531_na t_Measure_531_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (F F_129_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_51 (forall ((H_109_time Int)) (let ((.def_0 (exists ((t_Measure_530_time Int)(t_Measure_530_ba Bool)(t_Measure_530_na Int)(t_Measure_530_bb Bool)) (let ((.def_0 (forall ((F_128_time Int)) (let ((.def_0 (+ H_109_time 0))) (let ((.def_1 (<= .def_0 F_128_time))) (let ((.def_2 (<= F_128_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (not .def_3))) (let ((.def_5 (F F_128_time))) (let ((.def_6 (not .def_5))) (let ((.def_7 (or .def_6 .def_4))) .def_7)))))))))))(let ((.def_1 (= H_109_time t_Measure_530_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_530_time t_Measure_530_ba t_Measure_530_na t_Measure_530_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H H_109_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_52 (forall ((F_127_time Int)) (let ((.def_0 (exists ((t_Measure_529_time Int)(t_Measure_529_ba Bool)(t_Measure_529_na Int)(t_Measure_529_bb Bool)) (let ((.def_0 (exists ((t_G_147_time Int)) (let ((.def_0 (+ F_127_time 0))) (let ((.def_1 (<= .def_0 t_G_147_time))) (let ((.def_2 (+ F_127_time 5))) (let ((.def_3 (<= t_G_147_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_147_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_529_bb))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (exists ((t_H_54_time Int)) (let ((.def_0 (+ F_127_time 0))) (let ((.def_1 (<= .def_0 t_H_54_time))) (let ((.def_2 (+ F_127_time 10))) (let ((.def_3 (<= t_H_54_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (H t_H_54_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_6 (not t_Measure_529_bb))) (let ((.def_7 (or .def_1 .def_6))) (let ((.def_8 (or .def_7 .def_5))) (let ((.def_9 (and .def_8 .def_4))) (let ((.def_10 (= F_127_time t_Measure_529_time))) (let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (Measure t_Measure_529_time t_Measure_529_ba t_Measure_529_na t_Measure_529_bb))) (let ((.def_13 (and .def_12 .def_11))) .def_13)))))))))))))))))(let ((.def_1 (F F_127_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_53 (forall ((E_145_time Int)) (let ((.def_0 (exists ((t_Measure_528_time Int)(t_Measure_528_ba Bool)(t_Measure_528_na Int)(t_Measure_528_bb Bool)) (let ((.def_0 (exists ((t_G_146_time Int)) (let ((.def_0 (+ E_145_time 0))) (let ((.def_1 (<= .def_0 t_G_146_time))) (let ((.def_2 (+ E_145_time 10))) (let ((.def_3 (<= t_G_146_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_146_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 1 t_Measure_528_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_148_time Int)) (let ((.def_0 (+ E_145_time 0))) (let ((.def_1 (<= .def_0 G_148_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_145_time 10))) (let ((.def_4 (<= G_148_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_148_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_528_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_145_time t_Measure_528_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_528_time t_Measure_528_ba t_Measure_528_na t_Measure_528_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_145_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_54 (forall ((E_144_time Int)) (let ((.def_0 (exists ((t_Measure_527_time Int)(t_Measure_527_ba Bool)(t_Measure_527_na Int)(t_Measure_527_bb Bool)) (let ((.def_0 (exists ((t_G_145_time Int)) (let ((.def_0 (+ E_144_time 0))) (let ((.def_1 (<= .def_0 t_G_145_time))) (let ((.def_2 (+ E_144_time 10))) (let ((.def_3 (<= t_G_145_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_145_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 3 t_Measure_527_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_147_time Int)) (let ((.def_0 (+ E_144_time 0))) (let ((.def_1 (<= .def_0 G_147_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_144_time 10))) (let ((.def_4 (<= G_147_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_147_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_527_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_144_time t_Measure_527_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_527_time t_Measure_527_ba t_Measure_527_na t_Measure_527_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_144_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_55 (forall ((E_143_time Int)) (let ((.def_0 (exists ((t_Measure_526_time Int)(t_Measure_526_ba Bool)(t_Measure_526_na Int)(t_Measure_526_bb Bool)) (let ((.def_0 (exists ((t_G_144_time Int)) (let ((.def_0 (+ E_143_time 0))) (let ((.def_1 (<= .def_0 t_G_144_time))) (let ((.def_2 (+ E_143_time 10))) (let ((.def_3 (<= t_G_144_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_144_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_526_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (forall ((G_146_time Int)) (let ((.def_0 (+ E_143_time 0))) (let ((.def_1 (<= .def_0 G_146_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_143_time 10))) (let ((.def_4 (<= G_146_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_146_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_7 (not .def_2))) (let ((.def_8 (or .def_1 .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (and .def_9 .def_5))) (let ((.def_11 (not t_Measure_526_ba))) (let ((.def_12 (or .def_11 .def_10))) (let ((.def_13 (= E_143_time t_Measure_526_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_526_time t_Measure_526_ba t_Measure_526_na t_Measure_526_bb))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (E E_143_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_56 (forall ((E_142_time Int)) (let ((.def_0 (exists ((t_Measure_525_time Int)(t_Measure_525_ba Bool)(t_Measure_525_na Int)(t_Measure_525_bb Bool)) (let ((.def_0 (exists ((t_F_72_time Int)) (let ((.def_0 (+ E_142_time 0))) (let ((.def_1 (<= .def_0 t_F_72_time))) (let ((.def_2 (+ E_142_time 5))) (let ((.def_3 (<= t_F_72_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (F t_F_72_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< 2 t_Measure_525_na))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 t_Measure_525_ba))) (let ((.def_5 (or .def_4 .def_1))) (let ((.def_6 (or .def_5 .def_0))) (let ((.def_7 (exists ((t_G_143_time Int)) (let ((.def_0 (+ E_142_time 0))) (let ((.def_1 (<= .def_0 t_G_143_time))) (let ((.def_2 (+ E_142_time 10))) (let ((.def_3 (<= t_G_143_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (G t_G_143_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_8 (not t_Measure_525_ba))) (let ((.def_9 (or .def_3 .def_8))) (let ((.def_10 (or .def_9 .def_7))) (let ((.def_11 (forall ((G_145_time Int)) (let ((.def_0 (+ E_142_time 0))) (let ((.def_1 (<= .def_0 G_145_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ E_142_time 20))) (let ((.def_4 (<= G_145_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (G G_145_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_12 (not .def_2))) (let ((.def_13 (or .def_1 .def_12))) (let ((.def_14 (or .def_13 .def_11))) (let ((.def_15 (and .def_14 .def_10 .def_6))) (let ((.def_16 (= E_142_time t_Measure_525_time))) (let ((.def_17 (and .def_16 .def_15))) (let ((.def_18 (Measure t_Measure_525_time t_Measure_525_ba t_Measure_525_na t_Measure_525_bb))) (let ((.def_19 (and .def_18 .def_17))) .def_19)))))))))))))))))))))))(let ((.def_1 (E E_142_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_57 (forall ((C_200_time Int)) (let ((.def_0 (exists ((t_Measure_522_time Int)(t_Measure_522_ba Bool)(t_Measure_522_na Int)(t_Measure_522_bb Bool)) (let ((.def_0 (exists ((t_Measure_523_time Int)(t_Measure_523_ba Bool)(t_Measure_523_na Int)(t_Measure_523_bb Bool)) (let ((.def_0 (exists ((t_Measure_524_time Int)(t_Measure_524_ba Bool)(t_Measure_524_na Int)(t_Measure_524_bb Bool)) (let ((.def_0 (exists ((t_D_269_time Int)) (let ((.def_0 (+ t_Measure_524_time 0))) (let ((.def_1 (<= .def_0 t_D_269_time))) (let ((.def_2 (+ t_Measure_524_time 10))) (let ((.def_3 (<= t_D_269_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_269_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (exists ((t_E_75_time Int)) (let ((.def_0 (+ t_Measure_524_time 0))) (let ((.def_1 (<= .def_0 t_E_75_time))) (let ((.def_2 (<= t_E_75_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (E t_E_75_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_523_time 40))) (let ((.def_4 (= .def_3 t_Measure_524_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_524_time t_Measure_524_ba t_Measure_524_na t_Measure_524_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_268_time Int)) (let ((.def_0 (+ t_Measure_523_time 0))) (let ((.def_1 (<= .def_0 t_D_268_time))) (let ((.def_2 (+ t_Measure_523_time 40))) (let ((.def_3 (<= t_D_268_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_268_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_522_time 250))) (let ((.def_4 (= .def_3 t_Measure_523_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_523_time t_Measure_523_ba t_Measure_523_na t_Measure_523_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_267_time Int)) (let ((.def_0 (+ C_200_time 0))) (let ((.def_1 (<= .def_0 t_D_267_time))) (let ((.def_2 (+ C_200_time 250))) (let ((.def_3 (<= t_D_267_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_267_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_200_time t_Measure_522_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_522_time t_Measure_522_ba t_Measure_522_na t_Measure_522_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_200_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_58 (forall ((C_199_time Int)) (let ((.def_0 (exists ((t_Measure_521_time Int)(t_Measure_521_ba Bool)(t_Measure_521_na Int)(t_Measure_521_bb Bool)) (let ((.def_0 (exists ((t_E_74_time Int)) (let ((.def_0 (+ C_199_time 0))) (let ((.def_1 (<= .def_0 t_E_74_time))) (let ((.def_2 (+ C_199_time 250))) (let ((.def_3 (<= t_E_74_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (E t_E_74_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_199_time t_Measure_521_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_521_time t_Measure_521_ba t_Measure_521_na t_Measure_521_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_199_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_59 (forall ((C_198_time Int)) (let ((.def_0 (exists ((t_Measure_518_time Int)(t_Measure_518_ba Bool)(t_Measure_518_na Int)(t_Measure_518_bb Bool)) (let ((.def_0 (exists ((t_Measure_519_time Int)(t_Measure_519_ba Bool)(t_Measure_519_na Int)(t_Measure_519_bb Bool)) (let ((.def_0 (exists ((t_Measure_520_time Int)(t_Measure_520_ba Bool)(t_Measure_520_na Int)(t_Measure_520_bb Bool)) (let ((.def_0 (exists ((t_D_266_time Int)) (let ((.def_0 (+ t_Measure_520_time 0))) (let ((.def_1 (<= .def_0 t_D_266_time))) (let ((.def_2 (+ t_Measure_520_time 10))) (let ((.def_3 (<= t_D_266_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_266_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_520_ba))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (and true .def_4))) (let ((.def_6 (+ t_Measure_519_time 40))) (let ((.def_7 (= .def_6 t_Measure_520_time))) (let ((.def_8 (and .def_7 .def_5))) (let ((.def_9 (Measure t_Measure_520_time t_Measure_520_ba t_Measure_520_na t_Measure_520_bb))) (let ((.def_10 (and .def_9 .def_8))) .def_10))))))))))))))(let ((.def_1 (exists ((t_D_265_time Int)) (let ((.def_0 (+ t_Measure_519_time 0))) (let ((.def_1 (<= .def_0 t_D_265_time))) (let ((.def_2 (+ t_Measure_519_time 40))) (let ((.def_3 (<= t_D_265_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_265_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_518_time 250))) (let ((.def_4 (= .def_3 t_Measure_519_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_519_time t_Measure_519_ba t_Measure_519_na t_Measure_519_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_264_time Int)) (let ((.def_0 (+ C_198_time 0))) (let ((.def_1 (<= .def_0 t_D_264_time))) (let ((.def_2 (+ C_198_time 250))) (let ((.def_3 (<= t_D_264_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_264_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_198_time t_Measure_518_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_518_time t_Measure_518_ba t_Measure_518_na t_Measure_518_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_198_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_60 (forall ((C_197_time Int)) (let ((.def_0 (exists ((t_Measure_515_time Int)(t_Measure_515_ba Bool)(t_Measure_515_na Int)(t_Measure_515_bb Bool)) (let ((.def_0 (exists ((t_Measure_516_time Int)(t_Measure_516_ba Bool)(t_Measure_516_na Int)(t_Measure_516_bb Bool)) (let ((.def_0 (exists ((t_Measure_517_time Int)(t_Measure_517_ba Bool)(t_Measure_517_na Int)(t_Measure_517_bb Bool)) (let ((.def_0 (exists ((t_D_263_time Int)) (let ((.def_0 (+ t_Measure_517_time 0))) (let ((.def_1 (<= .def_0 t_D_263_time))) (let ((.def_2 (+ t_Measure_517_time 10))) (let ((.def_3 (<= t_D_263_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_263_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_516_time 40))) (let ((.def_2 (= .def_1 t_Measure_517_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_517_time t_Measure_517_ba t_Measure_517_na t_Measure_517_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_262_time Int)) (let ((.def_0 (+ t_Measure_516_time 0))) (let ((.def_1 (<= .def_0 t_D_262_time))) (let ((.def_2 (+ t_Measure_516_time 40))) (let ((.def_3 (<= t_D_262_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_262_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (+ t_Measure_515_time 250))) (let ((.def_4 (= .def_3 t_Measure_516_time))) (let ((.def_5 (and .def_4 .def_2))) (let ((.def_6 (Measure t_Measure_516_time t_Measure_516_ba t_Measure_516_na t_Measure_516_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (exists ((t_D_261_time Int)) (let ((.def_0 (+ C_197_time 0))) (let ((.def_1 (<= .def_0 t_D_261_time))) (let ((.def_2 (+ C_197_time 250))) (let ((.def_3 (<= t_D_261_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_261_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_197_time t_Measure_515_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_515_time t_Measure_515_ba t_Measure_515_na t_Measure_515_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_197_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_61 (forall ((C_196_time Int)) (let ((.def_0 (exists ((t_Measure_513_time Int)(t_Measure_513_ba Bool)(t_Measure_513_na Int)(t_Measure_513_bb Bool)) (let ((.def_0 (exists ((t_Measure_514_time Int)(t_Measure_514_ba Bool)(t_Measure_514_na Int)(t_Measure_514_bb Bool)) (let ((.def_0 (exists ((t_D_260_time Int)) (let ((.def_0 (+ t_Measure_514_time 0))) (let ((.def_1 (<= .def_0 t_D_260_time))) (let ((.def_2 (+ t_Measure_514_time 51))) (let ((.def_3 (<= t_D_260_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_260_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_513_time 250))) (let ((.def_2 (= .def_1 t_Measure_514_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_514_time t_Measure_514_ba t_Measure_514_na t_Measure_514_bb))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (exists ((t_D_259_time Int)) (let ((.def_0 (+ C_196_time 0))) (let ((.def_1 (<= .def_0 t_D_259_time))) (let ((.def_2 (+ C_196_time 250))) (let ((.def_3 (<= t_D_259_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_259_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= C_196_time t_Measure_513_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_513_time t_Measure_513_ba t_Measure_513_na t_Measure_513_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (C C_196_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_62 (forall ((C_195_time Int)) (let ((.def_0 (exists ((t_Measure_512_time Int)(t_Measure_512_ba Bool)(t_Measure_512_na Int)(t_Measure_512_bb Bool)) (let ((.def_0 (exists ((t_D_258_time Int)) (let ((.def_0 (+ C_195_time 0))) (let ((.def_1 (<= .def_0 t_D_258_time))) (let ((.def_2 (+ C_195_time 301))) (let ((.def_3 (<= t_D_258_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_258_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_195_time t_Measure_512_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_512_time t_Measure_512_ba t_Measure_512_na t_Measure_512_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_195_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_63 (forall ((C_194_time Int)) (let ((.def_0 (exists ((t_Measure_511_time Int)(t_Measure_511_ba Bool)(t_Measure_511_na Int)(t_Measure_511_bb Bool)) (let ((.def_0 (exists ((t_D_257_time Int)) (let ((.def_0 (+ C_194_time 0))) (let ((.def_1 (<= .def_0 t_D_257_time))) (let ((.def_2 (+ C_194_time 300))) (let ((.def_3 (<= t_D_257_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (D t_D_257_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= C_194_time t_Measure_511_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_511_time t_Measure_511_ba t_Measure_511_na t_Measure_511_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (C C_194_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_64 (forall ((A_143_time Int)) (let ((.def_0 (exists ((t_Measure_510_time Int)(t_Measure_510_ba Bool)(t_Measure_510_na Int)(t_Measure_510_bb Bool)) (let ((.def_0 (exists ((t_C_96_time Int)) (let ((.def_0 (+ A_143_time 0))) (let ((.def_1 (<= .def_0 t_C_96_time))) (let ((.def_2 (<= t_C_96_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_96_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_510_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= A_143_time t_Measure_510_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_510_time t_Measure_510_ba t_Measure_510_na t_Measure_510_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (A A_143_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_65 (forall ((B_110_time Int)) (let ((.def_0 (exists ((t_Measure_509_time Int)(t_Measure_509_ba Bool)(t_Measure_509_na Int)(t_Measure_509_bb Bool)) (let ((.def_0 (exists ((t_C_95_time Int)) (let ((.def_0 (+ B_110_time 0))) (let ((.def_1 (<= .def_0 t_C_95_time))) (let ((.def_2 (<= t_C_95_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_95_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 100 t_Measure_509_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_110_time t_Measure_509_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_509_time t_Measure_509_ba t_Measure_509_na t_Measure_509_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_110_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_66 (forall ((B_109_time Int)) (let ((.def_0 (exists ((t_Measure_508_time Int)(t_Measure_508_ba Bool)(t_Measure_508_na Int)(t_Measure_508_bb Bool)) (let ((.def_0 (exists ((t_C_94_time Int)) (let ((.def_0 (+ B_109_time 0))) (let ((.def_1 (<= .def_0 t_C_94_time))) (let ((.def_2 (<= t_C_94_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (C t_C_94_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 50 t_Measure_508_na))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= B_109_time t_Measure_508_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_508_time t_Measure_508_ba t_Measure_508_na t_Measure_508_bb))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (B B_109_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_67 (forall ((A_142_time Int)) (let ((.def_0 (exists ((t_Measure_507_time Int)(t_Measure_507_ba Bool)(t_Measure_507_na Int)(t_Measure_507_bb Bool)) (let ((.def_0 (exists ((t_B_91_time Int)) (let ((.def_0 (+ A_142_time 0))) (let ((.def_1 (<= .def_0 t_B_91_time))) (let ((.def_2 (<= t_B_91_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_91_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (or .def_1 t_Measure_507_ba))) (let ((.def_3 (or .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) (let ((.def_5 (and true .def_4))) (let ((.def_6 (= A_142_time t_Measure_507_time))) (let ((.def_7 (and .def_6 .def_5))) (let ((.def_8 (Measure t_Measure_507_time t_Measure_507_ba t_Measure_507_na t_Measure_507_bb))) (let ((.def_9 (and .def_8 .def_7))) .def_9)))))))))))))(let ((.def_1 (A A_142_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_68 (forall ((A_141_time Int)) (let ((.def_0 (exists ((t_Measure_506_time Int)(t_Measure_506_ba Bool)(t_Measure_506_na Int)(t_Measure_506_bb Bool)) (let ((.def_0 (exists ((t_B_90_time Int)) (let ((.def_0 (+ A_141_time 0))) (let ((.def_1 (<= .def_0 t_B_90_time))) (let ((.def_2 (<= t_B_90_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_90_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not t_Measure_506_ba))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= A_141_time t_Measure_506_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_506_time t_Measure_506_ba t_Measure_506_na t_Measure_506_bb))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (A A_141_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_69 (forall ((A_140_time Int)) (let ((.def_0 (exists ((t_Measure_505_time Int)(t_Measure_505_ba Bool)(t_Measure_505_na Int)(t_Measure_505_bb Bool)) (let ((.def_0 (exists ((t_B_89_time Int)) (let ((.def_0 (+ A_140_time 0))) (let ((.def_1 (<= .def_0 t_B_89_time))) (let ((.def_2 (<= t_B_89_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (B t_B_89_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (= A_140_time t_Measure_505_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_505_time t_Measure_505_ba t_Measure_505_na t_Measure_505_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (A A_140_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_70 (exists ((t_H_53_time Int)) (let ((.def_0 (exists ((t_Measure_504_time Int)(t_Measure_504_ba Bool)(t_Measure_504_na Int)(t_Measure_504_bb Bool)) (let ((.def_0 (forall ((F_126_time Int)) (let ((.def_0 (+ t_H_53_time 0))) (let ((.def_1 (<= .def_0 F_126_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_H_53_time 10))) (let ((.def_4 (<= F_126_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (F F_126_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (= t_H_53_time t_Measure_504_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_504_time t_Measure_504_ba t_Measure_504_na t_Measure_504_bb))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (H t_H_53_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_71 (and .def_70 .def_69 .def_68 .def_67 .def_66 .def_65 .def_64 .def_63 .def_62 .def_61 .def_60 .def_59 .def_58 .def_57 .def_56 .def_55 .def_54 .def_53 .def_52 .def_51 .def_50 .def_49 .def_48 .def_43 .def_38 .def_33 .def_28 .def_23 .def_18 .def_13 .def_8 .def_7 .def_6 .def_5 .def_4 .def_3 .def_2 .def_1 .def_0))) .def_71)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
