Require Import List String QArith.
Require Import BBSL.BBSL BBSL.Interval BBSL.BB.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.

Definition lead_vehicle_decelerating : Spec :=
(CND (EXP_Bvar "前方車両がある")
,[("追従"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "追従区間" (EXP_BBvar "追従区間")]
 ,EXP_Ioverlap (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "追従区間")))
 ;
 ("減速"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "減速区間" (EXP_BBvar "減速区間")]
 ,EXP_Ioverlap (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "減速区間")))
 ;
 ("停止"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "追従区間" (EXP_BBvar "追従区間")
  ;DEF_BB "減速区間" (EXP_BBvar "減速区間")]
 ,EXP_and (EXP_Ilt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "追従区間"))) (EXP_Ilt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "減速区間"))))
 ;
 ("レスポンス無し"
 ,[DEF_BB "前方車両" (EXP_BBvar "前方車両")
  ;DEF_BB "追従区間" (EXP_BBvar "追従区間")
  ;DEF_BB "減速区間" (EXP_BBvar "減速区間")]
 ,EXP_and (EXP_Igt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "追従区間"))) (EXP_Igt (EXP_projy(EXP_BBvar "前方車両")) (EXP_projy(EXP_BBvar "減速区間"))))]).