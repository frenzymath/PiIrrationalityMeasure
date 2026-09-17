import Formalization.PrimeSavingRounding

/-! Kernel-checked integer certificates for the rounded endpoint sum. -/

namespace PiIrrationality

set_option maxRecDepth 100000
-- Each certificate reduces 32 exact rational endpoint differences.
set_option maxHeartbeats 2000000

def roundedSavingChunkCertificate (k : ℕ) : ℤ :=
  ([118153571809180677441735127215475740,
    1004915829139732982881352991580761,
    347997197113336887828471449423855,
    180013318837481619180114070602614,
    111553072337805504550979410234471,
    76725552908564828834467304160222,
    56492309817810474908337731365166,
    43642601485165669183314418572585,
    34941701195391581534446588073575,
    28757760080932939334267589910812,
    24192944947095485849317086255923,
    20669884672196087474106206336575,
    17524437118043147299063896055069,
    14966458816523246162528612388976,
    12925049839570495457298604673169,
    11270388651594756209025640150845,
    9910953337470501863320644065749,
    8780730559110288025461865506531,
    7831142990268362518886871736270,
    7025806193441705629946659528760,
    6337035983747691248064135576691,
    5743469028176252659016154736516,
    5228408988810163351951088389931,
    4778656033913434161910373183910,
    4383664811011163364470197684661,
    4034929655778400862295375171749,
    3725529592520591429986256193502,
    3449787388164395616499160595753,
    3203011135652289712387418356623,
    2981296313651975714492165759137,
    2781372681914584434745372239484,
    2600484777760954253663933626821,
    2436297848431317440675546636368,
    2286823219356641148813524439679,
    2148596933251474910223871638635,
    1973311759372214296458966930541,
    1791919836274269638213441288968,
    1626200894177989687948802579117,
    1474460930080234090351813138939,
    1335224741690866237512067179208,
    1207203201334915188647646918736,
    1089266068596441438120543260369,
    980419299540791741456603157784,
    879786025362675157833677063908,
    786590540215164152210157069362,
    700144768344457640990497178912,
    619836783086350871459626641823,
    545121031212505649166615815013,
    475509980402956449268786153624,
    410566958950049778503115543565,
    349899997981175734186252187866,
    293156519683668032691723470764,
    240018741893797641772335491837,
    190199691268679360351986090889,
    143439735106636932166507043133,
    99503556511605896582426650598,
    58177509635921383515431334894,
    19267301678572846344835799450,
    24224808166580187358984097933,
    67723969135984782450880188487,
    106606944700740429066005959128,
    141479531549465407613135816326,
    172853578945377874572523678018,
    201163699864970909200246204849,
    226780645095054633589669634828,
    250022076254700160468857753764,
    271161296732909503883959918331,
    290434368480217030562998418927,
    308045944712568958278583326644,
    324174074889495700705782330336,
    338974182415932208499834828448,
    352582372789426744094842343698,
    365118197038565742180216362667,
    376686969837957721316886340899,
    387381721845401617239570581588,
    397284850255992344969813258155,
    406469519310351455134515201361,
    415000852780757231715894217322,
    422936952722289444021675065519,
    430329772583810021828869912003,
    437225867794222702315527743890,
    443667042917484536401780734695,
    449690911207249987503088112245,
    455331379734536999024009028394,
    460619071088625563363536415297,
    465581690867513092658251366649,
    470244348704565826669962157673] : List ℤ).getD k 0

theorem roundedSavingChunk_0 : roundedSavingChunk 0 = 118153571809180677441735127215475740 := by
  decide +kernel

theorem roundedSavingChunk_1 : roundedSavingChunk 1 = 1004915829139732982881352991580761 := by
  decide +kernel

theorem roundedSavingChunk_2 : roundedSavingChunk 2 = 347997197113336887828471449423855 := by
  decide +kernel

theorem roundedSavingChunk_3 : roundedSavingChunk 3 = 180013318837481619180114070602614 := by
  decide +kernel

theorem roundedSavingChunk_4 : roundedSavingChunk 4 = 111553072337805504550979410234471 := by
  decide +kernel

theorem roundedSavingChunk_5 : roundedSavingChunk 5 = 76725552908564828834467304160222 := by
  decide +kernel

theorem roundedSavingChunk_6 : roundedSavingChunk 6 = 56492309817810474908337731365166 := by
  decide +kernel

theorem roundedSavingChunk_7 : roundedSavingChunk 7 = 43642601485165669183314418572585 := by
  decide +kernel

theorem roundedSavingChunk_8 : roundedSavingChunk 8 = 34941701195391581534446588073575 := by
  decide +kernel

theorem roundedSavingChunk_9 : roundedSavingChunk 9 = 28757760080932939334267589910812 := by
  decide +kernel

theorem roundedSavingChunk_10 : roundedSavingChunk 10 = 24192944947095485849317086255923 := by
  decide +kernel

theorem roundedSavingChunk_11 : roundedSavingChunk 11 = 20669884672196087474106206336575 := by
  decide +kernel

theorem roundedSavingChunk_12 : roundedSavingChunk 12 = 17524437118043147299063896055069 := by
  decide +kernel

theorem roundedSavingChunk_13 : roundedSavingChunk 13 = 14966458816523246162528612388976 := by
  decide +kernel

theorem roundedSavingChunk_14 : roundedSavingChunk 14 = 12925049839570495457298604673169 := by
  decide +kernel

theorem roundedSavingChunk_15 : roundedSavingChunk 15 = 11270388651594756209025640150845 := by
  decide +kernel

theorem roundedSavingChunk_16 : roundedSavingChunk 16 = 9910953337470501863320644065749 := by
  decide +kernel

theorem roundedSavingChunk_17 : roundedSavingChunk 17 = 8780730559110288025461865506531 := by
  decide +kernel

theorem roundedSavingChunk_18 : roundedSavingChunk 18 = 7831142990268362518886871736270 := by
  decide +kernel

theorem roundedSavingChunk_19 : roundedSavingChunk 19 = 7025806193441705629946659528760 := by
  decide +kernel

theorem roundedSavingChunk_20 : roundedSavingChunk 20 = 6337035983747691248064135576691 := by
  decide +kernel

theorem roundedSavingChunk_21 : roundedSavingChunk 21 = 5743469028176252659016154736516 := by
  decide +kernel

theorem roundedSavingChunk_22 : roundedSavingChunk 22 = 5228408988810163351951088389931 := by
  decide +kernel

theorem roundedSavingChunk_23 : roundedSavingChunk 23 = 4778656033913434161910373183910 := by
  decide +kernel

theorem roundedSavingChunk_24 : roundedSavingChunk 24 = 4383664811011163364470197684661 := by
  decide +kernel

theorem roundedSavingChunk_25 : roundedSavingChunk 25 = 4034929655778400862295375171749 := by
  decide +kernel

theorem roundedSavingChunk_26 : roundedSavingChunk 26 = 3725529592520591429986256193502 := by
  decide +kernel

theorem roundedSavingChunk_27 : roundedSavingChunk 27 = 3449787388164395616499160595753 := by
  decide +kernel

theorem roundedSavingChunk_28 : roundedSavingChunk 28 = 3203011135652289712387418356623 := by
  decide +kernel

theorem roundedSavingChunk_29 : roundedSavingChunk 29 = 2981296313651975714492165759137 := by
  decide +kernel

theorem roundedSavingChunk_30 : roundedSavingChunk 30 = 2781372681914584434745372239484 := by
  decide +kernel

theorem roundedSavingChunk_31 : roundedSavingChunk 31 = 2600484777760954253663933626821 := by
  decide +kernel

theorem roundedSavingChunk_32 : roundedSavingChunk 32 = 2436297848431317440675546636368 := by
  decide +kernel

theorem roundedSavingChunk_33 : roundedSavingChunk 33 = 2286823219356641148813524439679 := by
  decide +kernel

theorem roundedSavingChunk_34 : roundedSavingChunk 34 = 2148596933251474910223871638635 := by
  decide +kernel

theorem roundedSavingChunk_35 : roundedSavingChunk 35 = 1973311759372214296458966930541 := by
  decide +kernel

theorem roundedSavingChunk_36 : roundedSavingChunk 36 = 1791919836274269638213441288968 := by
  decide +kernel

theorem roundedSavingChunk_37 : roundedSavingChunk 37 = 1626200894177989687948802579117 := by
  decide +kernel

theorem roundedSavingChunk_38 : roundedSavingChunk 38 = 1474460930080234090351813138939 := by
  decide +kernel

theorem roundedSavingChunk_39 : roundedSavingChunk 39 = 1335224741690866237512067179208 := by
  decide +kernel

theorem roundedSavingChunk_40 : roundedSavingChunk 40 = 1207203201334915188647646918736 := by
  decide +kernel

theorem roundedSavingChunk_41 : roundedSavingChunk 41 = 1089266068596441438120543260369 := by
  decide +kernel

theorem roundedSavingChunk_42 : roundedSavingChunk 42 = 980419299540791741456603157784 := by
  decide +kernel

theorem roundedSavingChunk_43 : roundedSavingChunk 43 = 879786025362675157833677063908 := by
  decide +kernel

theorem roundedSavingChunk_44 : roundedSavingChunk 44 = 786590540215164152210157069362 := by
  decide +kernel

theorem roundedSavingChunk_45 : roundedSavingChunk 45 = 700144768344457640990497178912 := by
  decide +kernel

theorem roundedSavingChunk_46 : roundedSavingChunk 46 = 619836783086350871459626641823 := by
  decide +kernel

theorem roundedSavingChunk_47 : roundedSavingChunk 47 = 545121031212505649166615815013 := by
  decide +kernel

theorem roundedSavingChunk_48 : roundedSavingChunk 48 = 475509980402956449268786153624 := by
  decide +kernel

theorem roundedSavingChunk_49 : roundedSavingChunk 49 = 410566958950049778503115543565 := by
  decide +kernel

theorem roundedSavingChunk_50 : roundedSavingChunk 50 = 349899997981175734186252187866 := by
  decide +kernel

theorem roundedSavingChunk_51 : roundedSavingChunk 51 = 293156519683668032691723470764 := by
  decide +kernel

theorem roundedSavingChunk_52 : roundedSavingChunk 52 = 240018741893797641772335491837 := by
  decide +kernel

theorem roundedSavingChunk_53 : roundedSavingChunk 53 = 190199691268679360351986090889 := by
  decide +kernel

theorem roundedSavingChunk_54 : roundedSavingChunk 54 = 143439735106636932166507043133 := by
  decide +kernel

theorem roundedSavingChunk_55 : roundedSavingChunk 55 = 99503556511605896582426650598 := by
  decide +kernel

theorem roundedSavingChunk_56 : roundedSavingChunk 56 = 58177509635921383515431334894 := by
  decide +kernel

theorem roundedSavingChunk_57 : roundedSavingChunk 57 = 19267301678572846344835799450 := by
  decide +kernel

theorem roundedSavingChunk_58 : roundedSavingChunk 58 = 24224808166580187358984097933 := by
  decide +kernel

theorem roundedSavingChunk_59 : roundedSavingChunk 59 = 67723969135984782450880188487 := by
  decide +kernel

theorem roundedSavingChunk_60 : roundedSavingChunk 60 = 106606944700740429066005959128 := by
  decide +kernel

theorem roundedSavingChunk_61 : roundedSavingChunk 61 = 141479531549465407613135816326 := by
  decide +kernel

theorem roundedSavingChunk_62 : roundedSavingChunk 62 = 172853578945377874572523678018 := by
  decide +kernel

theorem roundedSavingChunk_63 : roundedSavingChunk 63 = 201163699864970909200246204849 := by
  decide +kernel

theorem roundedSavingChunk_64 : roundedSavingChunk 64 = 226780645095054633589669634828 := by
  decide +kernel

theorem roundedSavingChunk_65 : roundedSavingChunk 65 = 250022076254700160468857753764 := by
  decide +kernel

theorem roundedSavingChunk_66 : roundedSavingChunk 66 = 271161296732909503883959918331 := by
  decide +kernel

theorem roundedSavingChunk_67 : roundedSavingChunk 67 = 290434368480217030562998418927 := by
  decide +kernel

theorem roundedSavingChunk_68 : roundedSavingChunk 68 = 308045944712568958278583326644 := by
  decide +kernel

theorem roundedSavingChunk_69 : roundedSavingChunk 69 = 324174074889495700705782330336 := by
  decide +kernel

theorem roundedSavingChunk_70 : roundedSavingChunk 70 = 338974182415932208499834828448 := by
  decide +kernel

theorem roundedSavingChunk_71 : roundedSavingChunk 71 = 352582372789426744094842343698 := by
  decide +kernel

theorem roundedSavingChunk_72 : roundedSavingChunk 72 = 365118197038565742180216362667 := by
  decide +kernel

theorem roundedSavingChunk_73 : roundedSavingChunk 73 = 376686969837957721316886340899 := by
  decide +kernel

theorem roundedSavingChunk_74 : roundedSavingChunk 74 = 387381721845401617239570581588 := by
  decide +kernel

theorem roundedSavingChunk_75 : roundedSavingChunk 75 = 397284850255992344969813258155 := by
  decide +kernel

theorem roundedSavingChunk_76 : roundedSavingChunk 76 = 406469519310351455134515201361 := by
  decide +kernel

theorem roundedSavingChunk_77 : roundedSavingChunk 77 = 415000852780757231715894217322 := by
  decide +kernel

theorem roundedSavingChunk_78 : roundedSavingChunk 78 = 422936952722289444021675065519 := by
  decide +kernel

theorem roundedSavingChunk_79 : roundedSavingChunk 79 = 430329772583810021828869912003 := by
  decide +kernel

theorem roundedSavingChunk_80 : roundedSavingChunk 80 = 437225867794222702315527743890 := by
  decide +kernel

theorem roundedSavingChunk_81 : roundedSavingChunk 81 = 443667042917484536401780734695 := by
  decide +kernel

theorem roundedSavingChunk_82 : roundedSavingChunk 82 = 449690911207249987503088112245 := by
  decide +kernel

theorem roundedSavingChunk_83 : roundedSavingChunk 83 = 455331379734536999024009028394 := by
  decide +kernel

theorem roundedSavingChunk_84 : roundedSavingChunk 84 = 460619071088625563363536415297 := by
  decide +kernel

theorem roundedSavingChunk_85 : roundedSavingChunk 85 = 465581690867513092658251366649 := by
  decide +kernel

theorem roundedSavingChunk_86 : roundedSavingChunk 86 = 470244348704565826669962157673 := by
  decide +kernel

theorem roundedSavingChunk_eq_certificate (k : ℕ) (hk : k < 87) :
    roundedSavingChunk k = roundedSavingChunkCertificate k := by
  interval_cases k
  · exact roundedSavingChunk_0
  · exact roundedSavingChunk_1
  · exact roundedSavingChunk_2
  · exact roundedSavingChunk_3
  · exact roundedSavingChunk_4
  · exact roundedSavingChunk_5
  · exact roundedSavingChunk_6
  · exact roundedSavingChunk_7
  · exact roundedSavingChunk_8
  · exact roundedSavingChunk_9
  · exact roundedSavingChunk_10
  · exact roundedSavingChunk_11
  · exact roundedSavingChunk_12
  · exact roundedSavingChunk_13
  · exact roundedSavingChunk_14
  · exact roundedSavingChunk_15
  · exact roundedSavingChunk_16
  · exact roundedSavingChunk_17
  · exact roundedSavingChunk_18
  · exact roundedSavingChunk_19
  · exact roundedSavingChunk_20
  · exact roundedSavingChunk_21
  · exact roundedSavingChunk_22
  · exact roundedSavingChunk_23
  · exact roundedSavingChunk_24
  · exact roundedSavingChunk_25
  · exact roundedSavingChunk_26
  · exact roundedSavingChunk_27
  · exact roundedSavingChunk_28
  · exact roundedSavingChunk_29
  · exact roundedSavingChunk_30
  · exact roundedSavingChunk_31
  · exact roundedSavingChunk_32
  · exact roundedSavingChunk_33
  · exact roundedSavingChunk_34
  · exact roundedSavingChunk_35
  · exact roundedSavingChunk_36
  · exact roundedSavingChunk_37
  · exact roundedSavingChunk_38
  · exact roundedSavingChunk_39
  · exact roundedSavingChunk_40
  · exact roundedSavingChunk_41
  · exact roundedSavingChunk_42
  · exact roundedSavingChunk_43
  · exact roundedSavingChunk_44
  · exact roundedSavingChunk_45
  · exact roundedSavingChunk_46
  · exact roundedSavingChunk_47
  · exact roundedSavingChunk_48
  · exact roundedSavingChunk_49
  · exact roundedSavingChunk_50
  · exact roundedSavingChunk_51
  · exact roundedSavingChunk_52
  · exact roundedSavingChunk_53
  · exact roundedSavingChunk_54
  · exact roundedSavingChunk_55
  · exact roundedSavingChunk_56
  · exact roundedSavingChunk_57
  · exact roundedSavingChunk_58
  · exact roundedSavingChunk_59
  · exact roundedSavingChunk_60
  · exact roundedSavingChunk_61
  · exact roundedSavingChunk_62
  · exact roundedSavingChunk_63
  · exact roundedSavingChunk_64
  · exact roundedSavingChunk_65
  · exact roundedSavingChunk_66
  · exact roundedSavingChunk_67
  · exact roundedSavingChunk_68
  · exact roundedSavingChunk_69
  · exact roundedSavingChunk_70
  · exact roundedSavingChunk_71
  · exact roundedSavingChunk_72
  · exact roundedSavingChunk_73
  · exact roundedSavingChunk_74
  · exact roundedSavingChunk_75
  · exact roundedSavingChunk_76
  · exact roundedSavingChunk_77
  · exact roundedSavingChunk_78
  · exact roundedSavingChunk_79
  · exact roundedSavingChunk_80
  · exact roundedSavingChunk_81
  · exact roundedSavingChunk_82
  · exact roundedSavingChunk_83
  · exact roundedSavingChunk_84
  · exact roundedSavingChunk_85
  · exact roundedSavingChunk_86

theorem roundedSavingTotal_value :
    roundedSavingTotal = 120256577336129180025431473189314502 := by
  unfold roundedSavingTotal
  rw [sum_list_range_int]
  have he : (∑ k ∈ Finset.range 87, roundedSavingChunk k) =
      ∑ k ∈ Finset.range 87, roundedSavingChunkCertificate k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact roundedSavingChunk_eq_certificate k (Finset.mem_range.mp hk)
  rw [he]
  decide +kernel

end PiIrrationality

