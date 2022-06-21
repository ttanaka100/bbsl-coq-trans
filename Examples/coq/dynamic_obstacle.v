Require Import List String QArith.
Require Import BBSL.BBSL BBSL.Interval BBSL.BB.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.

Definition dynamic_obstacle : Spec :=
(CND (EXP_Bvar "動的な障害物がある")
,[("障害物Aが自車線に侵入する可能性が高い"
 ,[DEF_SBB "未来つき障害物集合" (EXP_SBBvar "未来つき障害物集合")
  ;DEF_SBB "自車線" (EXP_SBBvar "自車線")]
 ,EXP_Qgt (EXP_RAT(EXP_SBBintersection (EXP_SBBvar "自車線") (EXP_SBBvar "未来つき障害物集合")) (EXP_SBBvar "未来つき障害物集合")) (EXP_Q 0.3))
 ;
 ("障害物Aが自車線に侵入する可能性が低い"
 ,[DEF_SBB "未来つき障害物集合" (EXP_SBBvar "未来つき障害物集合")
  ;DEF_SBB "自車線" (EXP_SBBvar "自車線")]
 ,EXP_forall "x" (EXP_SBBvar "未来つき障害物集合") (EXP_or (EXP_forall "y" (EXP_SBBvar "自車線") (EXP_not (EXP_BBoverlap (EXP_BBvar "x") (EXP_BBvar "y")))) (EXP_Qlt (EXP_RAT(EXP_SBBintersection (EXP_SBBvar "自車線") (EXP_SBBvar "未来つき障害物集合")) (EXP_SBBvar "未来つき障害物集合")) (EXP_Q 1.0e-2))))]).