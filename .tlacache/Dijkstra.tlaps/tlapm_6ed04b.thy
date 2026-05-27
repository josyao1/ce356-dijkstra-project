(* automatically generated -- do not edit manually *)
theory tlapm_6ed04b imports Constant Zenon begin
consts
  "isReal" :: c
  "isa_slas_a" :: "[c,c] => c"
  "isa_bksl_diva" :: "[c,c] => c"
  "isa_perc_a" :: "[c,c] => c"
  "isa_peri_peri_a" :: "[c,c] => c"
  "isInfinity" :: c
  "isa_lbrk_rbrk_a" :: "[c] => c"
  "isa_less_more_a" :: "[c] => c"

lemma ob'31: (* 2c3d620b9e45ca7af11934f241cdb5fe *)
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_Restrict_ suppressed *)
(* usable definition CONSTANT_Range_ suppressed *)
(* usable definition CONSTANT_Inverse_ suppressed *)
(* usable definition CONSTANT_IsInjective_ suppressed *)
(* usable definition CONSTANT_Injection_ suppressed *)
(* usable definition CONSTANT_Surjection_ suppressed *)
(* usable definition CONSTANT_Bijection_ suppressed *)
(* usable definition CONSTANT_ExistsInjection_ suppressed *)
(* usable definition CONSTANT_ExistsSurjection_ suppressed *)
(* usable definition CONSTANT_ExistsBijection_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_IsTransitivelyClosedOn_ suppressed *)
(* usable definition CONSTANT_IsWellFoundedOn_ suppressed *)
(* usable definition CONSTANT_SetLessThan_ suppressed *)
(* usable definition CONSTANT_WFDefOn_ suppressed *)
(* usable definition CONSTANT_OpDefinesFcn_ suppressed *)
(* usable definition CONSTANT_WFInductiveDefines_ suppressed *)
(* usable definition CONSTANT_WFInductiveUnique_ suppressed *)
(* usable definition CONSTANT_TransitiveClosureOn_ suppressed *)
(* usable definition CONSTANT_OpToRel_ suppressed *)
(* usable definition CONSTANT_PreImage_ suppressed *)
(* usable definition CONSTANT_LexPairOrdering_ suppressed *)
(* usable definition CONSTANT_LexProductOrdering_ suppressed *)
(* usable definition CONSTANT_FiniteSubsetsOf_ suppressed *)
(* usable definition CONSTANT_StrictSubsetOrdering_ suppressed *)
(* usable definition CONSTANT_EnabledWrapper_ suppressed *)
(* usable definition CONSTANT_CdotWrapper_ suppressed *)
fixes a_CONSTANTunde_Nunde_a
fixes a_CONSTANTunde_Kunde_a
fixes a_VARIABLEunde_xunde_a a_VARIABLEunde_xunde_a'
(* usable definition STATE_Init_ suppressed *)
(* usable definition STATE_Priv0_ suppressed *)
(* usable definition STATE_PrivI_ suppressed *)
(* usable definition STATE_Privileged_ suppressed *)
(* usable definition STATE_NumPrivileged_ suppressed *)
(* usable definition STATE_Legitimate_ suppressed *)
(* usable definition STATE_AtLeastOnePrivileged_ suppressed *)
(* usable definition ACTION_Act0_ suppressed *)
(* usable definition ACTION_ActI_ suppressed *)
(* usable definition ACTION_Next_ suppressed *)
(* usable definition TEMPORAL_Spec_ suppressed *)
(* usable definition TEMPORAL_FairSpec_ suppressed *)
(* usable definition TEMPORAL_SelfStabilization_ suppressed *)
(* usable definition CONSTANT_IsFiniteSet_ suppressed *)
(* usable definition CONSTANT_Cardinality_ suppressed *)
(* usable definition CONSTANT_Restrict_ suppressed *)
(* usable definition CONSTANT_Range_ suppressed *)
(* usable definition CONSTANT_Inverse_ suppressed *)
(* usable definition CONSTANT_IsInjective_ suppressed *)
(* usable definition CONSTANT_Injection_ suppressed *)
(* usable definition CONSTANT_Surjection_ suppressed *)
(* usable definition CONSTANT_Bijection_ suppressed *)
(* usable definition CONSTANT_ExistsInjection_ suppressed *)
(* usable definition CONSTANT_ExistsSurjection_ suppressed *)
(* usable definition CONSTANT_ExistsBijection_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_NatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefHypothesis_ suppressed *)
(* usable definition CONSTANT_FiniteNatInductiveDefConclusion_ suppressed *)
(* usable definition CONSTANT_IsTransitivelyClosedOn_ suppressed *)
(* usable definition CONSTANT_IsWellFoundedOn_ suppressed *)
(* usable definition CONSTANT_SetLessThan_ suppressed *)
(* usable definition CONSTANT_WFDefOn_ suppressed *)
(* usable definition CONSTANT_OpDefinesFcn_ suppressed *)
(* usable definition CONSTANT_WFInductiveDefines_ suppressed *)
(* usable definition CONSTANT_WFInductiveUnique_ suppressed *)
(* usable definition CONSTANT_TransitiveClosureOn_ suppressed *)
(* usable definition CONSTANT_OpToRel_ suppressed *)
(* usable definition CONSTANT_PreImage_ suppressed *)
(* usable definition CONSTANT_LexPairOrdering_ suppressed *)
(* usable definition CONSTANT_LexProductOrdering_ suppressed *)
(* usable definition CONSTANT_FiniteSubsetsOf_ suppressed *)
(* usable definition CONSTANT_StrictSubsetOrdering_ suppressed *)
(* usable definition STATE_TypeOK_ suppressed *)
fixes a_CONSTANTunde_yunde_a
assumes a_CONSTANTunde_yunde_a_in : "(a_CONSTANTunde_yunde_a \<in> ([((isa_peri_peri_a (((0)), (a_CONSTANTunde_Nunde_a)))) \<rightarrow> ((isa_peri_peri_a (((0)), ((arith_add ((a_CONSTANTunde_Kunde_a), ((minus (((Succ[0])))))))))))]))"
assumes v'230: "((a_CONSTANTunde_IsFiniteSetunde_a_1 ((subsetOf(((isa_peri_peri_a (((0)), (a_CONSTANTunde_Nunde_a)))), %a_CONSTANTunde_iunde_a. (cond((((a_CONSTANTunde_iunde_a) = ((0)))), (((fapply ((a_CONSTANTunde_yunde_a), ((0)))) = (fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_Nunde_a))))), (((fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_iunde_a))) \<noteq> (fapply ((a_CONSTANTunde_yunde_a), ((arith_add ((a_CONSTANTunde_iunde_a), ((minus (((Succ[0])))))))))))))))))))"
assumes v'231: "(((subsetOf(((isa_peri_peri_a (((0)), (a_CONSTANTunde_Nunde_a)))), %a_CONSTANTunde_iunde_a. (cond((((a_CONSTANTunde_iunde_a) = ((0)))), (((fapply ((a_CONSTANTunde_yunde_a), ((0)))) = (fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_Nunde_a))))), (((fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_iunde_a))) \<noteq> (fapply ((a_CONSTANTunde_yunde_a), ((arith_add ((a_CONSTANTunde_iunde_a), ((minus (((Succ[0])))))))))))))))) \<noteq> ({})))"
assumes v'232: "(((a_CONSTANTunde_IsFiniteSetunde_a (({})))) & (\<forall>a_CONSTANTunde_Sunde_a : ((((a_CONSTANTunde_IsFiniteSetunde_a ((a_CONSTANTunde_Sunde_a)))) \<Rightarrow> ((((((a_CONSTANTunde_Cardinalityunde_a ((a_CONSTANTunde_Sunde_a)))) = ((0)))) \<Leftrightarrow> (((a_CONSTANTunde_Sunde_a) = ({})))))))))"
assumes v'233: "((((a_CONSTANTunde_Cardinalityunde_a (({})))) = ((0))))"
shows "((((a_CONSTANTunde_Cardinalityunde_a_1 ((subsetOf(((isa_peri_peri_a (((0)), (a_CONSTANTunde_Nunde_a)))), %a_CONSTANTunde_iunde_a. (cond((((a_CONSTANTunde_iunde_a) = ((0)))), (((fapply ((a_CONSTANTunde_yunde_a), ((0)))) = (fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_Nunde_a))))), (((fapply ((a_CONSTANTunde_yunde_a), (a_CONSTANTunde_iunde_a))) \<noteq> (fapply ((a_CONSTANTunde_yunde_a), ((arith_add ((a_CONSTANTunde_iunde_a), ((minus (((Succ[0]))))))))))))))))))) \<noteq> ((0))))"(is "PROP ?ob'31")
proof -
show "PROP ?ob'31"
using assms by auto
qed
end
