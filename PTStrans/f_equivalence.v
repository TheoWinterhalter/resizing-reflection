(** The equivalence between PTS and PTSF.*)
Require Import base.
Require Import f_term f_env f_typ f_typ2 .
Require Import ut_term ut_red ut_env ut_typ ut_sr ut_typ_eq.
Require Import final_result.
Require Import List Lt Le Gt Plus Minus Peano_dec Compare_dec.
Require Import term red env typ_annot glue strip final_result.

Module f_equiv_mod (X:term_sig) (Y:pts_sig X) (TM:term_mod X) (EM: env_mod X TM) (RM: red_mod X TM) (UTM:ut_term_mod X) 
  (UEM: ut_env_mod X UTM) (URM: ut_red_mod X UTM) (PTS : ut_sr_mod X Y UTM UEM URM) (PTSe : ut_typ_eq_mod X Y UTM UEM URM PTS)
  (PTS_ATR: glue_mod X Y TM EM RM UTM UEM URM) (FTM: f_term_mod X) (FEM: f_env_mod X FTM).
Import X Y UTM UEM URM TM EM RM PTS PTSe PTS_ATR FTM FEM.
Include (final_mod X Y TM EM RM UTM UEM URM PTS PTSe PTS_ATR).
Include (f_typ2_mod  X Y FTM FEM UTM URM UEM PTS).



(** tactics for PTSeq2PTSF*)

(** This tactic will destruct an induction hypothesis H for the theorem PTSeq2PTSF, 
and then converts the context to Δ using context_conversion and then convert the types of the new terms to T.
If Δ or T is empty, no conversion is done for that part.*)

Ltac destruct_typ_equiv := fun H Δ T => 
let Γ := fresh "Γ" with HH := fresh "HH" with M := fresh "M" with N := fresh "N" with A := fresh "A" with eqΓ := fresh "eqΓ" 
with eqM := fresh "eqM" with eqN := fresh "eqN" with eqA := fresh "eqA" with HMN := fresh "HMN" with HM := fresh "HM" with HN := fresh "HN"  
with T0 := fresh "T" with S := fresh "S" with eqT := fresh "eqT" with eqS := fresh "eqS" with HT := fresh "HT" with H0 := fresh "H" 
with Hta := fresh "Hta" with HHta := fresh "HHta" with Δwf := fresh "Δwf" with eqΔ := fresh "eqΔ" with C := fresh "C" with D := fresh "D" 
with eqC := fresh "eqC" with eqD := fresh "eqD" with HCD := fresh "HCD" with hT := fresh "hT" with eqC1 := fresh "eqCC" 
with eqC2 := fresh "eqCCC" with T1 := fresh "TT" with eqT1 := fresh "eqTT" with HT1 := fresh "HHT" in
match (type of H) with
| exists _ _ _ _ _,_ => destruct H as (Γ&HH&M&N&A&eqΓ&eqM&eqN&eqA&HM&HN&HMN);
  match Δ with
  | True =>
      match T with
          | True => idtac
          | _ => destruct (erasure_equality _ _ _ _ T _ HMN HM HN) as (T0&S&eqT&eqS&?HT&?HS&hT&HT);[eauto|try (left;eauto;fail);right;eauto| ];
      rewrite eqM in eqT;rewrite eqN in eqS;clear M N eqM eqN HMN HM HN
      end
  | _ => assert (εc Δ = εc Γ) as eqΔ;[rewrite eqΓ;simpl;trivial;f_equal;trivial|];
      destruct context_conversion as (temp1&temp2&_);
      assert (Δ⊣) as Δwf;[(eapply wf_typ;eassumption)||(eapply wf_cons;eassumption)|];
      destruct (temp1 _ _ _ HM Δ Δwf) as (C&D&eqC&eqD&HCD);[symmetry;assumption|];rewrite eqM in eqC;rewrite eqA in eqD;clear HM;
      destruct (erasure_term _ T _ _ HCD) as (T0&eqT&HT);[eauto|try (left;eauto;fail);try (right;eauto;fail);eapply TypeCorrect;eassumption| ];
       rewrite <- eqT in eqC;clear C D eqT eqD HCD;
      destruct (temp1 _ _ _ HN Δ Δwf) as (C&D&eqC1&eqD&HCD);[symmetry;assumption|];rewrite eqN in eqC1;rewrite eqA in eqD;clear HN;
      destruct (erasure_term _ T _ _ HCD) as (T1&eqT1&HT1);[eauto|try (left;eauto;fail);try (right;eauto;fail);eapply TypeCorrect;eassumption| ];
       rewrite <- eqT1 in eqC1;clear C D eqT1 eqD HCD;
      destruct (temp2 _ _ _ _ HMN Δ Δwf) as (hT&C&D&eqC2&eqD&HCD);[symmetry;assumption|];
      rewrite eqM in eqC2;rewrite <- eqC in eqC2;rewrite eqN in eqD;rewrite <- eqC1 in eqD;
      destruct (erasure_equality2 _ _ _ _ _ _ _ _ HCD HT HT1 eqC2 eqD);
      clear M N Γ temp1 temp2 Δwf eqM eqN C D eqC2 eqD HCD hT eqΔ eqΓ HMN
  end
| _ => destruct H as (Γ&M&N&eqΓ&eqM&eqN&HMN);
  match Δ with
  | True => idtac
  | _ => assert (εc Δ = εc Γ) as eqΔ;[rewrite eqΓ;simpl;trivial;f_equal;trivial|];
      destruct context_conversion as (temp&_&_);
      destruct (temp _ _ _ HMN Δ) as (C&D&eqC&eqD&HCD);[(eapply wf_typ;eassumption)||(eapply wf_cons;eassumption)|symmetry;assumption|clear temp];
      try rewrite <- eqC in eqM;try rewrite <- eqD in eqN; clear M N Γ eqΓ eqΔ eqC eqD HMN;rename C into M, D into N,HCD into HMN 
  end;
  match T with
  | True => idtac
  | _ => destruct (erasure_term _ T _ _ HMN) as (T0&eqT&HT);[eauto|try (left;eauto;fail);right;eauto| ];
      rewrite <- eqT in eqM;clear M N eqT eqN HMN; rename eqM into eqT
  end
end;subst.

Ltac search_prod_equiv :=
let HeqX := fresh "HeqX" with Htp := fresh "Htp" with Hetp := fresh "Hetp" with s := fresh "s" in
match goal with
 | eq : ε ?x = (Π (?A), ?B)%UT,HT : _ ⊢ _ : ?x |- _ => 
 rewrite <- erasure_erasure_outer in eq at 1;remember (erasure_outer x) as X eqn:HeqX;
 destruct X;simpl in eq;try discriminate;[|symmetry in HeqX;apply erasure_outer_not_conv in HeqX; elim HeqX];
 destruct (TypeCorrect _ _ _ HT) as [(?&Htp)|(s&Htp)];[subst;simpl in HeqX;discriminate|];
 destruct (erasure_outer_typing _ _ _ Htp) as (?&Hetp);
 rewrite <- HeqX in Hetp;
 destruct (gen_pi _ _ _ _ Hetp) as (?s&?s&?s&?&_&?&?);injection eq;intros;subst
end.

(** The implication PTSeq -> PTSf*)

Theorem PTSeq2PTSF : (forall Γ M N  , Γ ⊢e M : N    ->exists Γ'   M' N'   ,εc Γ'=Γ/\ε M'=M/\ε N'=N/\                                    Γ' ⊢ M' : N')/\
                     (forall Γ M N A, Γ ⊢e M = N : A->exists Γ' H M' N' A',εc Γ'=Γ/\ε M'=M/\ε N'=N/\ε A'=A/\Γ' ⊢ M' : A'/\Γ' ⊢ N' : A'/\Γ' ⊢ H : M' = N')/\
                     (forall Γ      , Γ ⊣e          ->exists Γ'           ,εc Γ'=Γ/\                                                    Γ' ⊣).
apply (PTSe.typ_induc);intros.
(*sort*)
destruct H as (?&?&?). exists x,!s,!t;simpl;intuition.
(*var*)
destruct H as (?&?&?).
destruct (erasure_item_lift_rev _ _ _ _ H i) as (?&?&?);subst.
eexists x,#v,x0;simpl;intuition.
(*prod*)
destruct_typ_equiv H True !s.
destruct_typ_equiv H0 (T::Γ0) !t.
exists Γ0,(Π(T),T0),!u;intuition;eapply cProd;eassumption.
(*abs*)
destruct_typ_equiv H True !s1.
destruct_typ_equiv H0 (T::Γ0) !s2.
destruct_typ_equiv H1 (T::Γ0) T0.
exists Γ0,(λ[T],T1),(Π(T),T0);intuition;eapply cAbs;eassumption.
(*app*)
destruct_typ_equiv H True True.
search_prod_equiv.
destruct (erasure_term _ (Π (X1), X2) _ _ HMN) as (T0&eqT&HT5);[rewrite <- erasure_erasure_outer at 1;rewrite HeqX;trivial|try (left;eauto;fail);right;eauto| ].
destruct_typ_equiv H0 Γ0 X1.
exists Γ0,(T0·T),(X2 [ ← T]);simpl;rewrite erasure_subst;rewrite eqT;intuition;eapply cApp;eassumption.
(*conv*)
destruct_typ_equiv H True !s.
destruct_typ_equiv H0 Γ0 T.
(* exists Γ0,(T0∽hT),S;intuition;eapply cConv;eassumption. *)
(* (*sort-eq*) *)
(* destruct H as (?&?&?). *)
(* eexists x,_,!s,!s,!t;intuition;eapply cRefl;eapply cSort;eassumption. *)
(* (*var-eq*) *)
(* destruct H as (?&?&?);destruct (erasure_item_lift_rev _ _ _ _ H i) as (?&?&?). *)
(* eexists x,_,#v,#v,x0;intuition;eapply cRefl;eapply cVar;eassumption. *)
(* (*prod-eq*) *)
(* destruct_typ_equiv H True !s. *)
(* destruct_typ_equiv H0 (T::Γ0) !t. *)
(* assert (S :: Γ0 ⊢ (TT ↑ 1 # 1) [ ← #0 ∽ (hT †) ↑h 1] : !t). change !t with ((!t ↑ 1 # 1) [ ← #0 ∽ hT† ↑h 1]); eapply subst_typ; repeat (try eassumption;econstructor). *)
(* edestruct erasure_injectivity_term. eexact HHT. eapply subst_typ;[eexact H0|eexact HT|repeat (try eassumption;econstructor)..]. *)
(* rewrite erasure_lem2 at 1. rewrite erasure_lem2 at 1. reflexivity. *)
(* eexists Γ0,_,(Π(T),T0),(Π(S),(TT ↑ 1 # 1) [ ← #0 ∽ hT† ↑h 1]),!u;intuition;try eapply cProd;try eassumption. *)
(* simpl;f_equal;trivial. *)
(* simpl;rewrite erasure_subst. change (ε (#0%F ∽ hT ↑h 1 †)) with (ε #0). rewrite <- erasure_subst; rewrite_l_rev erasure_lem1;f_equal;trivial. *)
(* eapply cProdEq;try eassumption. *)
(* eapply cTrans;[eexact H|eassumption]. *)
(* (*abs-eq*) *)
(* destruct_typ_equiv H True !s. *)
(* destruct_typ_equiv H1 (T::Γ0) !t. *)
(* destruct_typ_equiv H0 (T::Γ0) T0. *)
(* assert (S :: Γ0 ⊢ (TT ↑ 1 # 1) [ ← #0 ∽ (hT †) ↑h 1] : (T0 ↑ 1 # 1) [ ← #0 ∽ hT† ↑h 1]). eapply subst_typ;repeat (try eassumption;econstructor). *)
(* assert (S :: Γ0 ⊢ (T0 ↑ 1 # 1) [ ← #0 ∽ (hT †) ↑h 1] : !t). change !t with ((!t ↑ 1 # 1) [ ← #0 ∽ hT† ↑h 1]); eapply subst_typ;repeat (try eassumption;econstructor). *)
(* edestruct erasure_injectivity_term. eexact HHT. eapply subst_typ; *)
(*   [eexact H0|eexact HT|repeat (try eassumption;econstructor)..]. rewrite erasure_lem2 at 1;rewrite erasure_lem2 at 1. reflexivity. *)
(* assert (Γ0 ⊢ {hT †, [S]ρ(T0 ↑ 1 # 1) [ ← #0 ∽ (hT †) ↑h 1]} : Π (S), (T0 ↑ 1 # 1) [ ← #0 ∽ (hT †) ↑h 1] = Π (T), T0). repeat econstructor;try eassumption. *)
(* subst. *)
(* eexists Γ0,_,(λ[T],T1),((λ[S],(TT ↑ 1 # 1) [ ← #0 ∽ hT† ↑h 1])∽_),(Π(T),T0);intuition;try eapply cAbs;try eassumption. *)
(* simpl;rewrite erasure_subst. change (ε (#0%F ∽ hT ↑h 1 †)) with (ε #0). rewrite <- erasure_subst; rewrite_l_rev erasure_lem1;f_equal;trivial. *)
(* eapply cConv;[econstructor;eassumption..|eassumption]. *)
(* eapply cTrans. Focus 2. eapply cIota. econstructor;eassumption. Focus 2. eassumption. econstructor;eassumption. *)
(* eapply cAbsEq;try eassumption. *)
(* eapply cTrans;[eexact H|eassumption]. *)
(* (*app-eq*) *)
(* destruct_typ_equiv H True True. *)
(* search_prod_equiv. *)
(* destruct (erasure_term _ (Π (X1), X2) _ _ HM) as (T0&eqT&HT5);[rewrite <- erasure_erasure_outer at 1;rewrite HeqX;trivial|try (left;eauto;fail);right;eauto| ]. *)
(* destruct (erasure_term _ (Π (X1), X2) _ _ HN) as (T1&eqT1&HT6);[rewrite <- erasure_erasure_outer at 1;rewrite HeqX;trivial|try (left;eauto;fail);right;eauto| ]. *)
(* edestruct erasure_equality2 as (L&HL). eexact HMN. eexact HT5. eexact HT6. symmetry;assumption. symmetry;assumption. *)
(* destruct_typ_equiv H0 Γ0 X1. *)
(* edestruct equality_subst as (K&HK); [eexact H2|eexact H|eassumption..|]. *)
(* eexists Γ0,_,(T0·T),((T1·TT)∽_),(X2 [ ← T]);simpl;rewrite erasure_subst;rewrite eqT;rewrite eqT1;intuition.  *)
(* eapply cApp;eassumption. *)
(* eapply cConv with (s:=s1). econstructor;eassumption. *)
(* change (!s1) with (!s1 [ ← T]);eapply substitution;try eassumption. *)
(* econstructor. econstructor;eassumption. eapply cSym;eassumption. *)
(* eapply cTrans with (T1 · TT).  *)
(* eapply cAppEq;eassumption. *)
(* eapply cIota with (s:=s1). econstructor;eassumption. Focus 2. econstructor;eassumption.  *)
(* change (!s1) with (!s1 [ ← T]). eapply substitution;try eassumption. *)
(* econstructor. econstructor;eassumption.  *)
(* (*sym*) *)
(* destruct_typ_equiv H True True. do 5 econstructor. intuition; eauto. *)
(* (*trans*) *)
(* destruct_typ_equiv H True True.  *)
(* destruct_typ_equiv H0 Γ0 A0. *)
(* eapply erasure_injectivity_term in eqC as (?&?);[|eassumption..]. *)
(* do 5 econstructor; intuition; eauto. *)
(* (*conv-eq*) *)
(* destruct_typ_equiv H True !s.  *)
(* destruct_typ_equiv H0 Γ0 T. *)
(* eexists Γ0,_,(T0∽_),(TT∽_),S;intuition;[eapply cConv;eassumption..|]. *)
(* eapply cTrans. eapply cSym;eapply cIota;try eassumption. *)
(* eapply cTrans. eassumption. eapply cIota;try eassumption. *)
(* (*beta*) *)
(* destruct_typ_equiv H True !s.  *)
(* destruct_typ_equiv H2 Γ0 T.  *)
(* destruct_typ_equiv H0 (T::Γ0) !t. *)
(* destruct_typ_equiv H1 (T::Γ0) T1. *)
(* eexists Γ0,_,((λ [T], T2) · T0),(T2 [ ← T0]),(T1 [ ← T0]);intuition;try eapply erasure_subst. *)
(* econstructor;[econstructor|];eassumption. *)
(* eapply substitution;try eassumption. econstructor. econstructor;eassumption. *)
(* eapply cBeta;eassumption. *)
(* (*nil*) *)
(* exists nil;intuition. *)
(* (*cons*) *)
(* destruct_typ_equiv H True !s. *)
(* exists (T::Γ0);intuition;econstructor;eassumption. *)
(* Qed. *)
Admitted.


Theorem PTSl2PTSF : (forall Γ M N,(Γ ⊢' M : N)%UT                                      -> exists Γ' M' N', εc Γ'=Γ/\ε M'=M/\ε N'=N/\Γ' ⊢ M' : N')/\
                    (forall Γ M N,(exists A B,(Γ ⊢' M : A)%UT/\(Γ ⊢' N : B)%UT/\ M ≡ N)-> exists Γ' M' N', εc Γ'=Γ/\ε M'=M/\ε N'=N/\Γ' ⊢ M' = N')/\
                    (forall Γ    ,(exists M N,(Γ ⊢' M : N)%UT)                         -> exists Γ'      , εc Γ'=Γ/\                Γ' ⊣).
repeat split;intros.
(*typ*)
apply PTS.legacy2typ in H as (?&?). apply PTS_equiv_PTSe in H. apply PTSeq2PTSF in H. 
assumption.
(*eq*)
destruct H as (?&?&?&?&?). apply PTS.legacy2typ in H as (?&?);apply PTS.legacy2typ in H0 as (?&?).
destruct (Betac_confl _ _ H1) as (?&?&?).
set (SubjectRed _ _ _ H _ H4);set (SubjectRed _ _ _ H0 _ H5).
destruct PTS_equiv_PTSe as (_&eq). 
destruct (eq Γ M x1 x) as (_&eq2).
destruct (eq Γ x1 N x0) as (_&eq3).
destruct PTSeq2PTSF as (_&eq2F&_).
apply eq2F in eq2;[|repeat split;try assumption;                econstructor;assumption].
apply eq2F in eq3;[|repeat split;try assumption;apply Betac_sym;econstructor;assumption].
destruct_typ_equiv eq2 True True.
destruct_typ_equiv eq3 True True.
destruct context_conversion as (_&temp&_).
assert (Γ0⊣) as Γ0wf;[eapply wf_typ;eassumption|].
destruct (temp _ _ _ _ HMN0 Γ0 Γ0wf) as (hT&C&D&eqC2&eqD&HCD);[assumption|].
rewrite eqM in eqC2;symmetry in eqC2.
edestruct equality_typing as ((?&?)&_). eexact HCD.
destruct (erasure_injectivity_term _ _ _ _ _ HN H6 eqC2).
do 3 econstructor. do 3 split. eassumption.
econstructor.
eapply cTrans. eassumption.
eapply cTrans; eassumption.
(*wf*)
destruct H as (?&?&?). 
apply PTS.legacy2typ in H as (?&?). apply PTS_equiv_PTSe in H. apply PTSeq2PTSF in H as (?&?&?&?&?&?&?).
subst;econstructor;repeat split. eapply wf_typ;eassumption.
Qed.

Theorem PTSF2PTSl : (forall Γ M N,Γ ⊢ M : N -> (εc Γ ⊢' ε M : ε N)%UT)/\
                    (forall Γ M N,Γ ⊢ M = N -> (exists A B,(εc Γ ⊢' ε M : A)%UT/\(εc Γ ⊢' ε N : B)%UT/\ ε M ≡ ε N))/\
                    (forall Γ    ,Γ ⊣       -> (εc Γ ⊣')%UT).
repeat split;intros.
(*typ*)
apply PTS.typ2legacy;apply PTSF2PTS;assumption.
(*eq*)
destruct H;edestruct equality_typing as ((?&?)&(?&?));[eexact H|].
do 2 econstructor;repeat split;try apply PTS.typ2legacy;try eapply PTSF2PTS;try eassumption.
(*wf*)
apply PTS.typ2legacy;apply PTSF2PTS;assumption.
Qed.

Theorem PTSlequivPTSF : (forall Γ M N,(Γ ⊢' M : N)%UT                                      <-> exists Γ' M' N', εc Γ'=Γ/\ε M'=M/\ε N'=N/\Γ' ⊢ M' : N')/\
                        (forall Γ M N,(exists A B,(Γ ⊢' M : A)%UT/\(Γ ⊢' N : B)%UT/\ M ≡ N)<-> exists Γ' M' N', εc Γ'=Γ/\ε M'=M/\ε N'=N/\Γ' ⊢ M' = N')/\
                        (forall Γ    ,(Γ ⊣')%UT                                            <-> exists Γ'      , εc Γ'=Γ/\                Γ' ⊣).
repeat split;intros;try (eapply PTSl2PTSF;eassumption);try (destruct H as (?&?&?&?&?&?&?);subst;eapply PTSF2PTSl;eassumption);
try (destruct H as (?&?&?);subst;eapply PTSF2PTSl;eassumption).
destruct H.
exists nil;repeat split;constructor.
apply PTSl2PTSF in H as (?&?&?&?&?&?&?);subst.
edestruct TypeCorrect as [(?&?)|(?&?)];[eexact H2| |].
subst;simpl in H1;injection H1;intros;subst.
exists (x0::x);repeat split;econstructor;eassumption.
edestruct erasure_injectivity_term_sort;[eexact H|eexact H1|].
edestruct equality_typing as (_&?&?);[eexact H0|].
edestruct gen_sort as (?&?&?);[eassumption| ]. subst.
eexists (x0∽_::x);repeat split;do 2 econstructor;try eassumption.
Qed.

Theorem Prod_Injective : forall Γ A B A' B' H, Γ ⊢ H : Π(A), B = Π(A'), B' -> exists H K, Γ ⊢ H : A = A' /\ A::Γ ⊢ K : B = (B'↑1#1)[←#0∽H↑h1].
intros.
edestruct equality_typing as ((?&?)&(?&?));[eexact H0|].
apply gen_pi in H1 as (?&?&?&?&?&?&?). apply gen_pi in H2 as (?&?&?&?&?&?&?);subst.
destruct PTSF2PTSl as (Htyp&Heq&_).
edestruct Heq as (_&_&_&_&?);[econstructor;eassumption|clear Heq].
simpl in *. edestruct URM.PiInj. eassumption.
destruct PTSl2PTSF as (_&Heq&_).
edestruct Heq as (?Γ&?A&?A'&?&?&?&?). do 2 econstructor;repeat split;[eapply Htyp;eexact H4|eapply Htyp;eexact H7|eassumption].
destruct H13.
eapply context_conversion in H13 as (?&?&?&?&?&?);[rewrite H11 in H13;rewrite H12 in H14|eapply wf_typ;eexact H7|assumption].
edestruct equality_typing as ((?&?)&(?&?));[eexact H15|].
eapply erasure_injectivity_term in H13 as (?&?);[apply cSym in H13|eassumption..].
eapply erasure_injectivity_term in H14 as (?&?);[                 |eassumption..].
assert (exists H,Γ ⊢ H : A = A') as (HH&?) by (econstructor;eapply cTrans;[eassumption|eapply cTrans;eassumption]).
replace ε B' with (ε ((B'↑1#1)[←#0∽HH↑h1])) in H9 by (symmetry;apply erasure_lem2).
assert (A :: Γ ⊢ (B' ↑ 1 # 1) [ ← #0 ∽ HH ↑h 1] : (!x5 ↑ 1 # 1) [ ← #0 ∽ HH ↑h 1]) as Btyp
by (eapply subst_typ;[eassumption..|do 2 econstructor|econstructor]);simpl in Btyp.
edestruct Heq as (?Γ&?B&?B'&?&?&?&?). do 2 econstructor;repeat split;[eapply Htyp;eexact H5|eapply Htyp;eassumption|eassumption].
destruct H22.
eapply context_conversion in H22 as (?&?&?&?&?&?);[rewrite H20 in H22;rewrite H21 in H23|eapply wf_typ;eexact H5|assumption].
edestruct equality_typing as ((?&?)&(?&?));[eexact H24|].
eapply erasure_injectivity_term in H22 as (?&?);[apply cSym in H22|eassumption..].
eapply erasure_injectivity_term in H23 as (?&?);[                 |eassumption..].
do 3 econstructor.
eassumption.
eapply cTrans;[eassumption|eapply cTrans;eassumption].
Qed.

End f_equiv_mod.

