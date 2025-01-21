(set-logic UFLIRA)
(declare-fun Measure (Int Bool Int Bool Int) Bool)
(declare-fun RetryAgreed_52_presence () Bool)
(declare-fun UserFallen_47_presence () Bool)
(declare-fun CurtainsOpened_33_presence () Bool)
(declare-fun RefuseRequest (Int) Bool)
(declare-fun DressingAbandoned_43_presence () Bool)
(declare-fun DressingStarted (Int) Bool)
(declare-fun Measure_22_presence () Bool)
(declare-fun SupportCalled (Int) Bool)
(declare-fun RetryAgreed (Int) Bool)
(declare-fun DressingStarted_70_presence () Bool)
(declare-fun SupportCalled_42_presence () Bool)
(declare-fun Measure_23_presence () Bool)
(declare-fun CurtainOpenRqt (Int) Bool)
(declare-fun UserFallen (Int) Bool)
(declare-fun Measure_21_presence () Bool)
(declare-fun CurtainsOpened (Int) Bool)
(declare-fun DressingAbandoned (Int) Bool)
(declare-fun RefuseRequest_32_presence () Bool)
(declare-fun DressingComplete (Int) Bool)
(declare-fun CurtainOpenRqt_38_presence () Bool)
(declare-fun DressingComplete_37_presence () Bool)
(assert (let ((.def_0 (forall ((Measure_23_time Int)(Measure_23_userUnderDressed Bool)(Measure_23_roomTemperature Int)(Measure_23_assentToSupportCalls Bool)(Measure_23_userDistressed Int)) (let ((.def_0 (<= 0 Measure_23_time))) (let ((.def_1 (and .def_0 true true true true))) (let ((.def_2 (=> Measure_23_presence .def_1))) (let ((.def_3 (Measure Measure_23_time Measure_23_userUnderDressed Measure_23_roomTemperature Measure_23_assentToSupportCalls Measure_23_userDistressed))) (let ((.def_4 (not .def_3))) (let ((.def_5 (or .def_4 .def_2))) .def_5)))))))))(let ((.def_1 (forall ((RetryAgreed_52_time Int)) (let ((.def_0 (<= 0 RetryAgreed_52_time))) (let ((.def_1 (=> RetryAgreed_52_presence .def_0))) (let ((.def_2 (RetryAgreed RetryAgreed_52_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_2 (forall ((SupportCalled_42_time Int)) (let ((.def_0 (<= 0 SupportCalled_42_time))) (let ((.def_1 (=> SupportCalled_42_presence .def_0))) (let ((.def_2 (SupportCalled SupportCalled_42_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_3 (forall ((UserFallen_47_time Int)) (let ((.def_0 (<= 0 UserFallen_47_time))) (let ((.def_1 (=> UserFallen_47_presence .def_0))) (let ((.def_2 (UserFallen UserFallen_47_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_4 (forall ((RefuseRequest_32_time Int)) (let ((.def_0 (<= 0 RefuseRequest_32_time))) (let ((.def_1 (=> RefuseRequest_32_presence .def_0))) (let ((.def_2 (RefuseRequest RefuseRequest_32_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_5 (forall ((CurtainsOpened_33_time Int)) (let ((.def_0 (<= 0 CurtainsOpened_33_time))) (let ((.def_1 (=> CurtainsOpened_33_presence .def_0))) (let ((.def_2 (CurtainsOpened CurtainsOpened_33_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_6 (forall ((CurtainOpenRqt_38_time Int)) (let ((.def_0 (<= 0 CurtainOpenRqt_38_time))) (let ((.def_1 (=> CurtainOpenRqt_38_presence .def_0))) (let ((.def_2 (CurtainOpenRqt CurtainOpenRqt_38_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_7 (forall ((DressingAbandoned_43_time Int)) (let ((.def_0 (<= 0 DressingAbandoned_43_time))) (let ((.def_1 (=> DressingAbandoned_43_presence .def_0))) (let ((.def_2 (DressingAbandoned DressingAbandoned_43_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_8 (forall ((DressingComplete_37_time Int)) (let ((.def_0 (<= 0 DressingComplete_37_time))) (let ((.def_1 (=> DressingComplete_37_presence .def_0))) (let ((.def_2 (DressingComplete DressingComplete_37_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_9 (forall ((DressingStarted_70_time Int)) (let ((.def_0 (<= 0 DressingStarted_70_time))) (let ((.def_1 (=> DressingStarted_70_presence .def_0))) (let ((.def_2 (DressingStarted DressingStarted_70_time))) (let ((.def_3 (not .def_2))) (let ((.def_4 (or .def_3 .def_1))) .def_4))))))))(let ((.def_10 (exists ((t_RetryAgreed_26_time Int)) (let ((.def_0 (forall ((RetryAgreed_51_time Int)) (let ((.def_0 (<= RetryAgreed_51_time t_RetryAgreed_26_time))) (let ((.def_1 (RetryAgreed RetryAgreed_51_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (RetryAgreed t_RetryAgreed_26_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_11 (exists ((t_RetryAgreed_25_time Int)) (let ((.def_0 (forall ((RetryAgreed_50_time Int)) (let ((.def_0 (<= t_RetryAgreed_25_time RetryAgreed_50_time))) (let ((.def_1 (RetryAgreed RetryAgreed_50_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (RetryAgreed t_RetryAgreed_25_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_12 (and .def_11 .def_10))) (let ((.def_13 (forall ((RetryAgreed_49_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (RetryAgreed RetryAgreed_49_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_14 (or .def_13 .def_12))) (let ((.def_15 (exists ((t_SupportCalled_52_time Int)) (let ((.def_0 (forall ((SupportCalled_41_time Int)) (let ((.def_0 (<= SupportCalled_41_time t_SupportCalled_52_time))) (let ((.def_1 (SupportCalled SupportCalled_41_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (SupportCalled t_SupportCalled_52_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_16 (exists ((t_SupportCalled_51_time Int)) (let ((.def_0 (forall ((SupportCalled_40_time Int)) (let ((.def_0 (<= t_SupportCalled_51_time SupportCalled_40_time))) (let ((.def_1 (SupportCalled SupportCalled_40_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (SupportCalled t_SupportCalled_51_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_17 (and .def_16 .def_15))) (let ((.def_18 (forall ((SupportCalled_39_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (SupportCalled SupportCalled_39_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_19 (or .def_18 .def_17))) (let ((.def_20 (exists ((t_UserFallen_15_time Int)) (let ((.def_0 (forall ((UserFallen_46_time Int)) (let ((.def_0 (<= UserFallen_46_time t_UserFallen_15_time))) (let ((.def_1 (UserFallen UserFallen_46_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (UserFallen t_UserFallen_15_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_21 (exists ((t_UserFallen_14_time Int)) (let ((.def_0 (forall ((UserFallen_45_time Int)) (let ((.def_0 (<= t_UserFallen_14_time UserFallen_45_time))) (let ((.def_1 (UserFallen UserFallen_45_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (UserFallen t_UserFallen_14_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_22 (and .def_21 .def_20))) (let ((.def_23 (forall ((UserFallen_44_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (UserFallen UserFallen_44_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_24 (or .def_23 .def_22))) (let ((.def_25 (exists ((t_RefuseRequest_22_time Int)) (let ((.def_0 (forall ((RefuseRequest_31_time Int)) (let ((.def_0 (<= RefuseRequest_31_time t_RefuseRequest_22_time))) (let ((.def_1 (RefuseRequest RefuseRequest_31_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (RefuseRequest t_RefuseRequest_22_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_26 (exists ((t_RefuseRequest_21_time Int)) (let ((.def_0 (forall ((RefuseRequest_30_time Int)) (let ((.def_0 (<= t_RefuseRequest_21_time RefuseRequest_30_time))) (let ((.def_1 (RefuseRequest RefuseRequest_30_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (RefuseRequest t_RefuseRequest_21_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_27 (and .def_26 .def_25))) (let ((.def_28 (forall ((RefuseRequest_29_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (RefuseRequest RefuseRequest_29_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_29 (or .def_28 .def_27))) (let ((.def_30 (exists ((t_CurtainsOpened_29_time Int)) (let ((.def_0 (forall ((CurtainsOpened_32_time Int)) (let ((.def_0 (<= CurtainsOpened_32_time t_CurtainsOpened_29_time))) (let ((.def_1 (CurtainsOpened CurtainsOpened_32_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (CurtainsOpened t_CurtainsOpened_29_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_31 (exists ((t_CurtainsOpened_28_time Int)) (let ((.def_0 (forall ((CurtainsOpened_31_time Int)) (let ((.def_0 (<= t_CurtainsOpened_28_time CurtainsOpened_31_time))) (let ((.def_1 (CurtainsOpened CurtainsOpened_31_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (CurtainsOpened t_CurtainsOpened_28_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_32 (and .def_31 .def_30))) (let ((.def_33 (forall ((CurtainsOpened_30_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (CurtainsOpened CurtainsOpened_30_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_34 (or .def_33 .def_32))) (let ((.def_35 (exists ((t_CurtainOpenRqt_16_time Int)) (let ((.def_0 (forall ((CurtainOpenRqt_37_time Int)) (let ((.def_0 (<= CurtainOpenRqt_37_time t_CurtainOpenRqt_16_time))) (let ((.def_1 (CurtainOpenRqt CurtainOpenRqt_37_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (CurtainOpenRqt t_CurtainOpenRqt_16_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_36 (exists ((t_CurtainOpenRqt_15_time Int)) (let ((.def_0 (forall ((CurtainOpenRqt_36_time Int)) (let ((.def_0 (<= t_CurtainOpenRqt_15_time CurtainOpenRqt_36_time))) (let ((.def_1 (CurtainOpenRqt CurtainOpenRqt_36_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (CurtainOpenRqt t_CurtainOpenRqt_15_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_37 (and .def_36 .def_35))) (let ((.def_38 (forall ((CurtainOpenRqt_35_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (CurtainOpenRqt CurtainOpenRqt_35_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_39 (or .def_38 .def_37))) (let ((.def_40 (exists ((t_DressingAbandoned_51_time Int)) (let ((.def_0 (forall ((DressingAbandoned_42_time Int)) (let ((.def_0 (<= DressingAbandoned_42_time t_DressingAbandoned_51_time))) (let ((.def_1 (DressingAbandoned DressingAbandoned_42_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingAbandoned t_DressingAbandoned_51_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_41 (exists ((t_DressingAbandoned_50_time Int)) (let ((.def_0 (forall ((DressingAbandoned_41_time Int)) (let ((.def_0 (<= t_DressingAbandoned_50_time DressingAbandoned_41_time))) (let ((.def_1 (DressingAbandoned DressingAbandoned_41_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingAbandoned t_DressingAbandoned_50_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_42 (and .def_41 .def_40))) (let ((.def_43 (forall ((DressingAbandoned_40_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (DressingAbandoned DressingAbandoned_40_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_44 (or .def_43 .def_42))) (let ((.def_45 (exists ((t_DressingComplete_65_time Int)) (let ((.def_0 (forall ((DressingComplete_36_time Int)) (let ((.def_0 (<= DressingComplete_36_time t_DressingComplete_65_time))) (let ((.def_1 (DressingComplete DressingComplete_36_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingComplete t_DressingComplete_65_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_46 (exists ((t_DressingComplete_64_time Int)) (let ((.def_0 (forall ((DressingComplete_35_time Int)) (let ((.def_0 (<= t_DressingComplete_64_time DressingComplete_35_time))) (let ((.def_1 (DressingComplete DressingComplete_35_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingComplete t_DressingComplete_64_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_47 (and .def_46 .def_45))) (let ((.def_48 (forall ((DressingComplete_34_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (DressingComplete DressingComplete_34_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_49 (or .def_48 .def_47))) (let ((.def_50 (exists ((t_DressingStarted_40_time Int)) (let ((.def_0 (forall ((DressingStarted_69_time Int)) (let ((.def_0 (<= DressingStarted_69_time t_DressingStarted_40_time))) (let ((.def_1 (DressingStarted DressingStarted_69_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingStarted t_DressingStarted_40_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_51 (exists ((t_DressingStarted_39_time Int)) (let ((.def_0 (forall ((DressingStarted_68_time Int)) (let ((.def_0 (<= t_DressingStarted_39_time DressingStarted_68_time))) (let ((.def_1 (DressingStarted DressingStarted_68_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_1 (DressingStarted t_DressingStarted_39_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_52 (and .def_51 .def_50))) (let ((.def_53 (forall ((DressingStarted_67_time Int)) (let ((.def_0 (not true))) (let ((.def_1 (DressingStarted DressingStarted_67_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_54 (or .def_53 .def_52))) (let ((.def_55 (forall ((Measure_21_time Int)(Measure_21_userUnderDressed Bool)(Measure_21_roomTemperature Int)(Measure_21_assentToSupportCalls Bool)(Measure_21_userDistressed Int)) (let ((.def_0 (forall ((Measure_22_time Int)(Measure_22_userUnderDressed Bool)(Measure_22_roomTemperature Int)(Measure_22_assentToSupportCalls Bool)(Measure_22_userDistressed Int)) (let ((.def_0 (= Measure_21_presence Measure_22_presence))) (let ((.def_1 (= Measure_21_userDistressed Measure_22_userDistressed))) (let ((.def_2 (= Measure_21_assentToSupportCalls Measure_22_assentToSupportCalls))) (let ((.def_3 (= Measure_21_roomTemperature Measure_22_roomTemperature))) (let ((.def_4 (= Measure_21_userUnderDressed Measure_22_userUnderDressed))) (let ((.def_5 (= Measure_21_time Measure_22_time))) (let ((.def_6 (and .def_5 .def_4 .def_3 .def_2 .def_1 .def_0))) (let ((.def_7 (not .def_5))) (let ((.def_8 (or .def_7 .def_6))) (let ((.def_9 (Measure Measure_22_time Measure_22_userUnderDressed Measure_22_roomTemperature Measure_22_assentToSupportCalls Measure_22_userDistressed))) (let ((.def_10 (not .def_9))) (let ((.def_11 (or .def_10 .def_8))) .def_11)))))))))))))))(let ((.def_1 (Measure Measure_21_time Measure_21_userUnderDressed Measure_21_roomTemperature Measure_21_assentToSupportCalls Measure_21_userDistressed))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_56 (forall ((UserFallen_43_time Int)) (let ((.def_0 (exists ((t_Measure_111_time Int)(t_Measure_111_userUnderDressed Bool)(t_Measure_111_roomTemperature Int)(t_Measure_111_assentToSupportCalls Bool)(t_Measure_111_userDistressed Int)) (let ((.def_0 (forall ((SupportCalled_38_time Int)) (let ((.def_0 (+ UserFallen_43_time 0))) (let ((.def_1 (<= .def_0 SupportCalled_38_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ UserFallen_43_time 120))) (let ((.def_4 (<= SupportCalled_38_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (SupportCalled SupportCalled_38_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (not t_Measure_111_assentToSupportCalls))) (let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= UserFallen_43_time t_Measure_111_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_111_time t_Measure_111_userUnderDressed t_Measure_111_roomTemperature t_Measure_111_assentToSupportCalls t_Measure_111_userDistressed))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (UserFallen UserFallen_43_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_57 (forall ((DressingStarted_66_time Int)) (let ((.def_0 (exists ((t_Measure_110_time Int)(t_Measure_110_userUnderDressed Bool)(t_Measure_110_roomTemperature Int)(t_Measure_110_assentToSupportCalls Bool)(t_Measure_110_userDistressed Int)) (let ((.def_0 (exists ((t_DressingComplete_63_time Int)) (let ((.def_0 (+ DressingStarted_66_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_63_time))) (let ((.def_2 (+ DressingStarted_66_time 60))) (let ((.def_3 (<= t_DressingComplete_63_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingComplete t_DressingComplete_63_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (exists ((t_DressingAbandoned_49_time Int)) (let ((.def_0 (+ DressingStarted_66_time 0))) (let ((.def_1 (<= .def_0 t_DressingAbandoned_49_time))) (let ((.def_2 (+ DressingStarted_66_time 120))) (let ((.def_3 (<= t_DressingAbandoned_49_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingAbandoned t_DressingAbandoned_49_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (not t_Measure_110_userUnderDressed))) (let ((.def_4 (< t_Measure_110_roomTemperature 16))) (let ((.def_5 (not .def_4))) (let ((.def_6 (and .def_5 .def_3))) (let ((.def_7 (or .def_6 .def_2))) (let ((.def_8 (= DressingStarted_66_time t_Measure_110_time))) (let ((.def_9 (and .def_8 .def_7))) (let ((.def_10 (Measure t_Measure_110_time t_Measure_110_userUnderDressed t_Measure_110_roomTemperature t_Measure_110_assentToSupportCalls t_Measure_110_userDistressed))) (let ((.def_11 (and .def_10 .def_9))) .def_11)))))))))))))))(let ((.def_1 (DressingStarted DressingStarted_66_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_58 (forall ((DressingAbandoned_39_time Int)) (let ((.def_0 (exists ((t_Measure_108_time Int)(t_Measure_108_userUnderDressed Bool)(t_Measure_108_roomTemperature Int)(t_Measure_108_assentToSupportCalls Bool)(t_Measure_108_userDistressed Int)) (let ((.def_0 (exists ((t_Measure_109_time Int)(t_Measure_109_userUnderDressed Bool)(t_Measure_109_roomTemperature Int)(t_Measure_109_assentToSupportCalls Bool)(t_Measure_109_userDistressed Int)) (let ((.def_0 (exists ((t_SupportCalled_50_time Int)) (let ((.def_0 (+ t_Measure_109_time 0))) (let ((.def_1 (<= .def_0 t_SupportCalled_50_time))) (let ((.def_2 (<= t_SupportCalled_50_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (SupportCalled t_SupportCalled_50_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (not t_Measure_109_assentToSupportCalls))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (and true .def_5))) (let ((.def_7 (+ t_Measure_108_time 1800))) (let ((.def_8 (= .def_7 t_Measure_109_time))) (let ((.def_9 (and .def_8 .def_6))) (let ((.def_10 (Measure t_Measure_109_time t_Measure_109_userUnderDressed t_Measure_109_roomTemperature t_Measure_109_assentToSupportCalls t_Measure_109_userDistressed))) (let ((.def_11 (and .def_10 .def_9))) .def_11)))))))))))))))(let ((.def_1 (exists ((t_RetryAgreed_24_time Int)) (let ((.def_0 (+ DressingAbandoned_39_time 0))) (let ((.def_1 (<= .def_0 t_RetryAgreed_24_time))) (let ((.def_2 (+ DressingAbandoned_39_time 1800))) (let ((.def_3 (<= t_RetryAgreed_24_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (RetryAgreed t_RetryAgreed_24_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= DressingAbandoned_39_time t_Measure_108_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_108_time t_Measure_108_userUnderDressed t_Measure_108_roomTemperature t_Measure_108_assentToSupportCalls t_Measure_108_userDistressed))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (DressingAbandoned DressingAbandoned_39_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_59 (forall ((UserFallen_42_time Int)) (let ((.def_0 (exists ((t_Measure_107_time Int)(t_Measure_107_userUnderDressed Bool)(t_Measure_107_roomTemperature Int)(t_Measure_107_assentToSupportCalls Bool)(t_Measure_107_userDistressed Int)) (let ((.def_0 (exists ((t_SupportCalled_49_time Int)) (let ((.def_0 (+ UserFallen_42_time 0))) (let ((.def_1 (<= .def_0 t_SupportCalled_49_time))) (let ((.def_2 (<= t_SupportCalled_49_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (SupportCalled t_SupportCalled_49_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (not t_Measure_107_assentToSupportCalls))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (and true .def_5))) (let ((.def_7 (= UserFallen_42_time t_Measure_107_time))) (let ((.def_8 (and .def_7 .def_6))) (let ((.def_9 (Measure t_Measure_107_time t_Measure_107_userUnderDressed t_Measure_107_roomTemperature t_Measure_107_assentToSupportCalls t_Measure_107_userDistressed))) (let ((.def_10 (and .def_9 .def_8))) .def_10))))))))))))))(let ((.def_1 (UserFallen UserFallen_42_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_60 (forall ((RetryAgreed_48_time Int)) (let ((.def_0 (exists ((t_Measure_106_time Int)(t_Measure_106_userUnderDressed Bool)(t_Measure_106_roomTemperature Int)(t_Measure_106_assentToSupportCalls Bool)(t_Measure_106_userDistressed Int)) (let ((.def_0 (exists ((t_DressingAbandoned_48_time Int)) (let ((.def_0 (<= RetryAgreed_48_time t_DressingAbandoned_48_time))) (let ((.def_1 (DressingAbandoned t_DressingAbandoned_48_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (exists ((t_DressingComplete_62_time Int)) (let ((.def_0 (<= RetryAgreed_48_time t_DressingComplete_62_time))) (let ((.def_1 (DressingComplete t_DressingComplete_62_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_2 (or .def_1 .def_0))) (let ((.def_3 (= RetryAgreed_48_time t_Measure_106_time))) (let ((.def_4 (and .def_3 .def_2))) (let ((.def_5 (Measure t_Measure_106_time t_Measure_106_userUnderDressed t_Measure_106_roomTemperature t_Measure_106_assentToSupportCalls t_Measure_106_userDistressed))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (RetryAgreed RetryAgreed_48_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_61 (forall ((RetryAgreed_47_time Int)) (let ((.def_0 (exists ((t_Measure_104_time Int)(t_Measure_104_userUnderDressed Bool)(t_Measure_104_roomTemperature Int)(t_Measure_104_assentToSupportCalls Bool)(t_Measure_104_userDistressed Int)) (let ((.def_0 (exists ((t_DressingStarted_38_time Int)) (let ((.def_0 (<= RetryAgreed_47_time t_DressingStarted_38_time))) (let ((.def_1 (DressingStarted t_DressingStarted_38_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_1 (not true))) (let ((.def_2 (= t_Measure_104_userDistressed 3))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (exists ((t_Measure_105_time Int)(t_Measure_105_userUnderDressed Bool)(t_Measure_105_roomTemperature Int)(t_Measure_105_assentToSupportCalls Bool)(t_Measure_105_userDistressed Int)) (let ((.def_0 (exists ((t_SupportCalled_48_time Int)) (let ((.def_0 (+ t_Measure_105_time 0))) (let ((.def_1 (<= .def_0 t_SupportCalled_48_time))) (let ((.def_2 (+ t_Measure_105_time 30))) (let ((.def_3 (<= t_SupportCalled_48_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (SupportCalled t_SupportCalled_48_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (+ t_Measure_104_time 30))) (let ((.def_2 (= .def_1 t_Measure_105_time))) (let ((.def_3 (and .def_2 .def_0))) (let ((.def_4 (Measure t_Measure_105_time t_Measure_105_userUnderDressed t_Measure_105_roomTemperature t_Measure_105_assentToSupportCalls t_Measure_105_userDistressed))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_7 (exists ((t_DressingStarted_37_time Int)) (let ((.def_0 (+ RetryAgreed_47_time 0))) (let ((.def_1 (<= .def_0 t_DressingStarted_37_time))) (let ((.def_2 (+ RetryAgreed_47_time 30))) (let ((.def_3 (<= t_DressingStarted_37_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingStarted t_DressingStarted_37_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_8 (or .def_7 .def_6))) (let ((.def_9 (not .def_2))) (let ((.def_10 (or .def_1 .def_9))) (let ((.def_11 (or .def_10 .def_8))) (let ((.def_12 (and .def_11 .def_5))) (let ((.def_13 (= RetryAgreed_47_time t_Measure_104_time))) (let ((.def_14 (and .def_13 .def_12))) (let ((.def_15 (Measure t_Measure_104_time t_Measure_104_userUnderDressed t_Measure_104_roomTemperature t_Measure_104_assentToSupportCalls t_Measure_104_userDistressed))) (let ((.def_16 (and .def_15 .def_14))) .def_16))))))))))))))))))))(let ((.def_1 (RetryAgreed RetryAgreed_47_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_62 (forall ((RetryAgreed_46_time Int)) (let ((.def_0 (exists ((t_Measure_103_time Int)(t_Measure_103_userUnderDressed Bool)(t_Measure_103_roomTemperature Int)(t_Measure_103_assentToSupportCalls Bool)(t_Measure_103_userDistressed Int)) (let ((.def_0 (exists ((t_DressingStarted_36_time Int)) (let ((.def_0 (+ RetryAgreed_46_time 1))) (let ((.def_1 (<= .def_0 t_DressingStarted_36_time))) (let ((.def_2 (+ RetryAgreed_46_time 30))) (let ((.def_3 (<= t_DressingStarted_36_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingStarted t_DressingStarted_36_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (= RetryAgreed_46_time t_Measure_103_time))) (let ((.def_2 (and .def_1 .def_0))) (let ((.def_3 (Measure t_Measure_103_time t_Measure_103_userUnderDressed t_Measure_103_roomTemperature t_Measure_103_assentToSupportCalls t_Measure_103_userDistressed))) (let ((.def_4 (and .def_3 .def_2))) .def_4))))))))(let ((.def_1 (RetryAgreed RetryAgreed_46_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_63 (forall ((DressingStarted_65_time Int)) (let ((.def_0 (exists ((t_Measure_102_time Int)(t_Measure_102_userUnderDressed Bool)(t_Measure_102_roomTemperature Int)(t_Measure_102_assentToSupportCalls Bool)(t_Measure_102_userDistressed Int)) (let ((.def_0 (exists ((t_SupportCalled_47_time Int)) (let ((.def_0 (+ DressingStarted_65_time 0))) (let ((.def_1 (<= .def_0 t_SupportCalled_47_time))) (let ((.def_2 (<= t_SupportCalled_47_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (SupportCalled t_SupportCalled_47_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (not true))) (let ((.def_2 (not t_Measure_102_assentToSupportCalls))) (let ((.def_3 (or .def_1 .def_2))) (let ((.def_4 (or .def_3 .def_1))) (let ((.def_5 (or .def_4 .def_0))) (let ((.def_6 (and true .def_5))) (let ((.def_7 (< 2 t_Measure_102_userDistressed))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) (let ((.def_10 (= DressingStarted_65_time t_Measure_102_time))) (let ((.def_11 (and .def_10 .def_9))) (let ((.def_12 (Measure t_Measure_102_time t_Measure_102_userUnderDressed t_Measure_102_roomTemperature t_Measure_102_assentToSupportCalls t_Measure_102_userDistressed))) (let ((.def_13 (and .def_12 .def_11))) .def_13)))))))))))))))))(let ((.def_1 (DressingStarted DressingStarted_65_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_64 (forall ((DressingStarted_64_time Int)) (let ((.def_0 (exists ((t_Measure_101_time Int)(t_Measure_101_userUnderDressed Bool)(t_Measure_101_roomTemperature Int)(t_Measure_101_assentToSupportCalls Bool)(t_Measure_101_userDistressed Int)) (let ((.def_0 (exists ((t_DressingAbandoned_47_time Int)) (let ((.def_0 (+ DressingStarted_64_time 0))) (let ((.def_1 (<= .def_0 t_DressingAbandoned_47_time))) (let ((.def_2 (<= t_DressingAbandoned_47_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (DressingAbandoned t_DressingAbandoned_47_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_1 (< 2 t_Measure_101_userDistressed))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) (let ((.def_4 (= DressingStarted_64_time t_Measure_101_time))) (let ((.def_5 (and .def_4 .def_3))) (let ((.def_6 (Measure t_Measure_101_time t_Measure_101_userUnderDressed t_Measure_101_roomTemperature t_Measure_101_assentToSupportCalls t_Measure_101_userDistressed))) (let ((.def_7 (and .def_6 .def_5))) .def_7)))))))))))(let ((.def_1 (DressingStarted DressingStarted_64_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_65 (forall ((DressingStarted_63_time Int)) (let ((.def_0 (exists ((t_Measure_100_time Int)(t_Measure_100_userUnderDressed Bool)(t_Measure_100_roomTemperature Int)(t_Measure_100_assentToSupportCalls Bool)(t_Measure_100_userDistressed Int)) (let ((.def_0 (exists ((t_DressingComplete_61_time Int)) (let ((.def_0 (+ DressingStarted_63_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_61_time))) (let ((.def_2 (+ DressingStarted_63_time 120))) (let ((.def_3 (<= t_DressingComplete_61_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingComplete t_DressingComplete_61_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (<= t_Measure_100_roomTemperature 22))) (let ((.def_3 (<= t_Measure_100_roomTemperature 11))) (let ((.def_4 (and .def_3 t_Measure_100_userUnderDressed))) (let ((.def_5 (or .def_1 .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (or .def_6 .def_1))) (let ((.def_8 (or .def_7 .def_0))) (let ((.def_9 (exists ((t_DressingComplete_60_time Int)) (let ((.def_0 (+ DressingStarted_63_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_60_time))) (let ((.def_2 (- 22 t_Measure_100_roomTemperature))) (let ((.def_3 (* .def_2 15))) (let ((.def_4 (- 120 .def_3))) (let ((.def_5 (* .def_4 1))) (let ((.def_6 (+ DressingStarted_63_time .def_5))) (let ((.def_7 (<= t_DressingComplete_60_time .def_6))) (let ((.def_8 (and .def_7 .def_1))) (let ((.def_9 (DressingComplete t_DressingComplete_60_time))) (let ((.def_10 (and .def_9 .def_8))) .def_10))))))))))))))(let ((.def_10 (not .def_2))) (let ((.def_11 (or .def_5 .def_10))) (let ((.def_12 (or .def_11 .def_9))) (let ((.def_13 (exists ((t_SupportCalled_46_time Int)) (let ((.def_0 (+ DressingStarted_63_time 0))) (let ((.def_1 (<= .def_0 t_SupportCalled_46_time))) (let ((.def_2 (<= t_SupportCalled_46_time .def_0))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (SupportCalled t_SupportCalled_46_time))) (let ((.def_5 (and .def_4 .def_3))) .def_5)))))))))(let ((.def_14 (not t_Measure_100_assentToSupportCalls))) (let ((.def_15 (or .def_1 .def_14))) (let ((.def_16 (or .def_15 .def_1))) (let ((.def_17 (or .def_16 .def_13))) (let ((.def_18 (and true .def_17))) (let ((.def_19 (not t_Measure_100_userUnderDressed))) (let ((.def_20 (not .def_3))) (let ((.def_21 (or .def_20 .def_19))) (let ((.def_22 (or .def_1 .def_21))) (let ((.def_23 (or .def_22 .def_18))) (let ((.def_24 (and .def_23 .def_12 .def_8))) (let ((.def_25 (exists ((t_DressingAbandoned_46_time Int)) (let ((.def_0 (+ DressingStarted_63_time 0))) (let ((.def_1 (<= .def_0 t_DressingAbandoned_46_time))) (let ((.def_2 (+ DressingStarted_63_time 120))) (let ((.def_3 (<= t_DressingAbandoned_46_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingAbandoned t_DressingAbandoned_46_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_26 (or .def_25 .def_24))) (let ((.def_27 (= DressingStarted_63_time t_Measure_100_time))) (let ((.def_28 (and .def_27 .def_26))) (let ((.def_29 (Measure t_Measure_100_time t_Measure_100_userUnderDressed t_Measure_100_roomTemperature t_Measure_100_assentToSupportCalls t_Measure_100_userDistressed))) (let ((.def_30 (and .def_29 .def_28))) .def_30))))))))))))))))))))))))))))))))))(let ((.def_1 (DressingStarted DressingStarted_63_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_66 (forall ((DressingStarted_62_time Int)) (let ((.def_0 (exists ((t_Measure_99_time Int)(t_Measure_99_userUnderDressed Bool)(t_Measure_99_roomTemperature Int)(t_Measure_99_assentToSupportCalls Bool)(t_Measure_99_userDistressed Int)) (let ((.def_0 (exists ((t_DressingComplete_59_time Int)) (let ((.def_0 (+ DressingStarted_62_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_59_time))) (let ((.def_2 (+ DressingStarted_62_time 120))) (let ((.def_3 (<= t_DressingComplete_59_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingComplete t_DressingComplete_59_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_1 (not true))) (let ((.def_2 (< t_Measure_99_roomTemperature 19))) (let ((.def_3 (< t_Measure_99_roomTemperature 17))) (let ((.def_4 (or .def_1 .def_3))) (let ((.def_5 (or .def_4 .def_2))) (let ((.def_6 (or .def_5 .def_1))) (let ((.def_7 (or .def_6 .def_0))) (let ((.def_8 (exists ((t_DressingComplete_58_time Int)) (let ((.def_0 (+ DressingStarted_62_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_58_time))) (let ((.def_2 (+ DressingStarted_62_time 90))) (let ((.def_3 (<= t_DressingComplete_58_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingComplete t_DressingComplete_58_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_9 (not .def_2))) (let ((.def_10 (or .def_4 .def_9))) (let ((.def_11 (or .def_10 .def_8))) (let ((.def_12 (exists ((t_DressingComplete_57_time Int)) (let ((.def_0 (+ DressingStarted_62_time 0))) (let ((.def_1 (<= .def_0 t_DressingComplete_57_time))) (let ((.def_2 (+ DressingStarted_62_time 60))) (let ((.def_3 (<= t_DressingComplete_57_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingComplete t_DressingComplete_57_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_13 (not .def_3))) (let ((.def_14 (or .def_1 .def_13))) (let ((.def_15 (or .def_14 .def_12))) (let ((.def_16 (and .def_15 .def_11 .def_7))) (let ((.def_17 (exists ((t_DressingAbandoned_45_time Int)) (let ((.def_0 (+ DressingStarted_62_time 0))) (let ((.def_1 (<= .def_0 t_DressingAbandoned_45_time))) (let ((.def_2 (+ DressingStarted_62_time 120))) (let ((.def_3 (<= t_DressingAbandoned_45_time .def_2))) (let ((.def_4 (and .def_3 .def_1))) (let ((.def_5 (DressingAbandoned t_DressingAbandoned_45_time))) (let ((.def_6 (and .def_5 .def_4))) .def_6))))))))))(let ((.def_18 (or .def_17 .def_16))) (let ((.def_19 (= DressingStarted_62_time t_Measure_99_time))) (let ((.def_20 (and .def_19 .def_18))) (let ((.def_21 (Measure t_Measure_99_time t_Measure_99_userUnderDressed t_Measure_99_roomTemperature t_Measure_99_assentToSupportCalls t_Measure_99_userDistressed))) (let ((.def_22 (and .def_21 .def_20))) .def_22))))))))))))))))))))))))))(let ((.def_1 (DressingStarted DressingStarted_62_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (or .def_2 .def_0))) .def_3)))))))(let ((.def_67 (exists ((t_CurtainOpenRqt_14_time Int)) (let ((.def_0 (exists ((t_Measure_98_time Int)(t_Measure_98_userUnderDressed Bool)(t_Measure_98_roomTemperature Int)(t_Measure_98_assentToSupportCalls Bool)(t_Measure_98_userDistressed Int)) (let ((.def_0 (forall ((CurtainsOpened_29_time Int)) (let ((.def_0 (+ t_CurtainOpenRqt_14_time 0))) (let ((.def_1 (<= .def_0 CurtainsOpened_29_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_CurtainOpenRqt_14_time 60))) (let ((.def_4 (<= CurtainsOpened_29_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (CurtainsOpened CurtainsOpened_29_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_1 (not t_Measure_98_userUnderDressed))) (let ((.def_2 (< 2 t_Measure_98_userDistressed))) (let ((.def_3 (not .def_2))) (let ((.def_4 (and true .def_3))) (let ((.def_5 (and .def_4 .def_1))) (let ((.def_6 (and .def_5 true))) (let ((.def_7 (and .def_6 .def_0))) (let ((.def_8 (forall ((RefuseRequest_28_time Int)) (let ((.def_0 (+ t_CurtainOpenRqt_14_time 0))) (let ((.def_1 (<= .def_0 RefuseRequest_28_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_CurtainOpenRqt_14_time 30))) (let ((.def_4 (<= RefuseRequest_28_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (RefuseRequest RefuseRequest_28_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_9 (and .def_4 t_Measure_98_userUnderDressed))) (let ((.def_10 (and .def_9 .def_8))) (let ((.def_11 (forall ((CurtainsOpened_28_time Int)) (let ((.def_0 (+ t_CurtainOpenRqt_14_time 0))) (let ((.def_1 (<= .def_0 CurtainsOpened_28_time))) (let ((.def_2 (not .def_1))) (let ((.def_3 (+ t_CurtainOpenRqt_14_time 60))) (let ((.def_4 (<= CurtainsOpened_28_time .def_3))) (let ((.def_5 (not .def_4))) (let ((.def_6 (or .def_5 .def_2))) (let ((.def_7 (CurtainsOpened CurtainsOpened_28_time))) (let ((.def_8 (not .def_7))) (let ((.def_9 (or .def_8 .def_6))) .def_9)))))))))))))(let ((.def_12 (and true .def_2))) (let ((.def_13 (and .def_12 .def_11))) (let ((.def_14 (or .def_13 .def_10 .def_7))) (let ((.def_15 (= t_CurtainOpenRqt_14_time t_Measure_98_time))) (let ((.def_16 (and .def_15 .def_14))) (let ((.def_17 (Measure t_Measure_98_time t_Measure_98_userUnderDressed t_Measure_98_roomTemperature t_Measure_98_assentToSupportCalls t_Measure_98_userDistressed))) (let ((.def_18 (and .def_17 .def_16))) .def_18))))))))))))))))))))))(let ((.def_1 (CurtainOpenRqt t_CurtainOpenRqt_14_time))) (let ((.def_2 (and .def_1 .def_0))) .def_2))))))(let ((.def_68 (and .def_67 .def_66 .def_65 .def_64 .def_63 .def_62 .def_61 .def_60 .def_59 .def_58 .def_57 .def_56 .def_55 .def_54 .def_49 .def_44 .def_39 .def_34 .def_29 .def_24 .def_19 .def_14 .def_9 .def_8 .def_7 .def_6 .def_5 .def_4 .def_3 .def_2 .def_1 .def_0))) .def_68))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
