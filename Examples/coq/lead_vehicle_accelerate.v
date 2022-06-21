Require Import List String QArith.
Require Import BBSL.BBSL BBSL.Interval BBSL.BB.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.

Definition lead_vehicle_accelerate : Spec :=
(CND (EXP_Bvar "前方車両がある")
,[("加速"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "加速区間" (EXP_BBvar "加速区間")]
 ,EXP_Ioverlap (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "加速区間")))
 ;
 ("追従"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "加速区間" (EXP_BBvar "加速区間")]
 ,EXP_Ilt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "加速区間")))
 ;
 ("レスポンス無し"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "加速区間" (EXP_BBvar "加速区間")]
 ,EXP_Igt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "加速区間")))]).