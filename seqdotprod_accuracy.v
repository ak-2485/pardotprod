Require Import vcfloat.VCFloat.
Require Import List.
Require Import seqdotprod_model.

Require Import Reals.
Open Scope R.

Definition rounded t r:=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition fma_no_overflow (t: type) (x y z: R) : Prop :=
  (Rabs (rounded t  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.

Definition Bmult_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs (rounded t  (x * y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Section NAN.
Variable NAN: Nans.

Definition default_rel (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma default_rel_sep_0 t : 
  default_rel t <> 0.
Proof. 
unfold default_rel; apply Rabs_lt_pos.
rewrite Rabs_pos_eq; [apply Rmult_lt_0_compat; try nra; apply bpow_gt_0 | 
  apply Rmult_le_pos; try nra; apply bpow_ge_0].
Qed.

Lemma default_rel_gt_0 t : 
  0 < default_rel t.
Proof. 
unfold default_rel.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Lemma generic_round_property:
  forall (t: type) (x: R),
exists delta epsilon : R,
  (Rabs delta <= default_rel t)%R /\
  (Rabs epsilon <= default_abs t)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
split; [ | split]; auto.
Qed.

Lemma fma_accurate: 
   forall (t: type) 
             x (FINx: Binary.is_finite (fprec t) (femax t) x = true) 
             y (FINy: Binary.is_finite (fprec t) (femax t) y = true) 
             z (FINz: Binary.is_finite (fprec t) (femax t) z = true)
          (FIN: fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z FINx FINy FINz).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y + FT2R z)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
fold (@BFMA NAN t) in H.
rewrite H.
apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma BMULT_accurate: 
   forall (t: type) x y (FIN: Bmult_no_overflow t (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BMULT t x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (mult_nan t) BinarySingleNaN.mode_NE x y).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
destruct H as [? _].
unfold BMULT, BINOP.
rewrite H.
apply generic_round_property.
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Import Lra.

Lemma fold_left_Rplus_Rplus:
 forall al b c, fold_left Rplus al (b+c) = c + fold_left Rplus al b.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Lemma fold_left_Rplus_0:
 forall al b , fold_left Rplus al b = b + fold_left Rplus al 0.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.


Local Definition FR2 {t: type} (x12: ftype t * ftype t) := (FT2R (fst x12), FT2R (snd x12)).


(* old statements 
Lemma summation_error:
  forall (A: Type) (t: type) (A2R: A->R) (Fplus: A -> ftype t -> ftype t)
    (P: Fplus_properties _ _ A2R Fplus),
   let D := default_rel t in 
   let E := default_abs t in 
  forall v: list A,
    Binary.is_finite (fprec t) (femax t) (fold_right Fplus neg_zero v) = true ->
    Rabs (FT2R (fold_right Fplus neg_zero v) - fold_right Rplus 0 (map A2R v)) <= 
               (INR (List.length v) - 1) * D * fold_right Rplus 0 (map Rabs (map A2R v)) 
                      + Fplus_low_order_error t (map A2R v).

Lemma dotprod_error: 
  forall (t: type) (n: nat) (v1 v2: list (ftype t)), 
    length v1 = n ->
    length v2 = n ->
   let prods := map (uncurry Rmult) (List.combine (map FT2R v1)  (map FT2R v2)) in
     Rabs (FT2R (dotprod t v1 v2) - sum prods)
        <= (INR n-1) * default_rel t *  sum (map Rabs prods)
                 + Fplus_low_order_error t (rev prods).
*)

Import List ListNotations.

Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

Definition error_rel (t: type) (n : nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    ((1 + d)^(n-1) - 1) * (Rabs r + e/d)
  else 0%R.

Inductive fma_dot_prod_rel {t : type} : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  : fma_dot_prod_rel  [] (neg_zero )
| fma_dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    fma_dot_prod_rel  l s ->
    fma_dot_prod_rel  (xy::l) (BFMA (fst xy) (snd xy) s).

Lemma fma_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) fp, 
    fma_dot_prod_rel (rev (List.combine v1 v2)) fp -> 
    dotprod t v1 v2 = fp.
Proof.
intros v1 v2. 
 unfold dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ intros. inversion H; subst; simpl. auto. }
intros. inversion H; subst; simpl.
specialize (IHl s H3 ). rewrite <- IHl; auto.
Qed.


Inductive R_dot_prod_rel : 
            list (R * R) -> R -> Prop :=
| R_dot_prod_rel_nil  : R_dot_prod_rel  [] 0%R
| R_dot_prod_rel_cons : forall l xy s,
    R_dot_prod_rel  l s ->
    R_dot_prod_rel  (xy::l)  (fst xy * snd xy + s).

Definition sum: list R -> R := fold_right Rplus 0%R.


Lemma sum_rev l:
sum l = sum (rev l).
Proof.
unfold sum. 
rewrite fold_left_rev_right.
replace (fun x y : R => y + x) with Rplus
 by (do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra).
induction l; simpl; auto.
rewrite IHl.
rewrite <- fold_left_Rplus_0; f_equal; nra.
Qed.

Lemma R_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) rp, 
   let prods := map (uncurry Rmult) (map FR2 (List.combine v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (List.combine v1 v2))) rp -> 
    sum prods = rp.
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- map_rev.
revert H. revert rp.
induction (rev (map FR2 (List.combine v1 v2))).
{ intros. inversion H; subst. auto. }
intros. inversion H; subst; simpl.
unfold sum in *.
specialize (IHl s H3). rewrite IHl.
f_equal. destruct a; simpl; auto.
Qed.

Lemma R_dot_prod_rel_single rs a:
R_dot_prod_rel [a] rs -> rs = (fst a * snd a).
Proof.
intros.
inversion H.
inversion H3; subst; nra.
Qed.

Definition Rabsp p : R * R := (Rabs (fst p), Rabs (snd p)).

Lemma R_dot_prod_rel_Rabs_eq :
forall l s,
R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
induction  l.
-
intros.
inversion H.
rewrite Rabs_R0.
nra.
-
intros.
inversion H; subst; clear H.
unfold Rabsp. destruct a; simpl.
replace (Rabs(Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- IHl; try apply Rabs_pos; auto.
Qed.


Lemma sum_rel_R_Rabs :
forall l s1 s2,
R_dot_prod_rel l s1 -> R_dot_prod_rel (map Rabsp l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold Rabsp; destruct a; simpl.
eapply Rle_trans; [
apply Rabs_triang |].
replace (Rabs (Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0).
eapply Rplus_le_compat; try nra.
rewrite Rabs_mult; nra.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
apply Rabs_pos.
Qed.

Lemma is_finite_fma_no_overflow (t : type) :
  forall fma x y z
  (HFINb : Binary.is_finite (fprec t) (femax t) fma = true)
  (HEQ   : fma = BFMA x y z),
  let ov := bpow Zaux.radix2 (femax t) in
  Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov.
Proof.
intros.
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
rewrite HEQ in HFINb.
assert (HFIN: Binary.is_finite (fprec t) (femax t) x = true /\
  Binary.is_finite (fprec t) (femax t) y = true /\ 
  Binary.is_finite (fprec t) (femax t) z = true).
{ unfold BFMA in HFINb. 
    destruct x; destruct y; destruct z; simpl in *; try discriminate; auto.
    all: destruct s; destruct s0; destruct s1; simpl in *; try discriminate; auto. }
destruct HFIN as (A & B & C).
unfold rounded, FT2R, ov in H.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE x y z A B C) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0.
assert (H1: Binary.B2FF _ _ (BFMA x y z) = Binary.B2FF _ _ fma) by
  (f_equal; auto).
unfold BFMA in H1.
rewrite H0 in H1; clear H0.
rewrite <- HEQ in HFINb.
destruct fma;
simpl; intros; try discriminate.
Qed.

Lemma is_finite_BMULT_no_overflow (t : type) :
  forall a x y 
  (HFINb : Binary.is_finite (fprec t) (femax t) a = true)
  (HEQ   : a = BMULT t x y ),
  let ov := bpow Zaux.radix2 (femax t) in
  Rabs (rounded t (FT2R x * FT2R y)) < ov.
Proof.
intros.
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
rewrite HEQ in HFINb.
unfold rounded, FT2R, ov in H.
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0.
assert (H1: Binary.B2FF _ _ (BMULT t x y ) = Binary.B2FF _ _ a) by
  (f_equal; auto).
unfold BMULT, BINOP in H1.
rewrite H0 in H1; clear H0.
rewrite <- HEQ in HFINb.
destruct a;
simpl; intros; try discriminate.
Qed.

Lemma length_not_empty_lt {A} l :
l <> [] -> 
0 < INR (@length A l).
Proof.
intros.
destruct l.
destruct H; auto.
simpl (length (a:: l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
apply Rcomplements.Rlt_minus_l.
field_simplify.
simpl.
eapply Rlt_le_trans with 0;  try nra.
apply pos_INR.
Qed.

Lemma length_not_empty_nat' {A} l :
l <> [] -> 
(0 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply Rlt_le.
apply length_not_empty_lt;auto.
Qed.

Lemma dotprod_error: 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> forall fp rp rp_abs,
  let ov := bpow Zaux.radix2 (femax t) in
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
    R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp -> 
  R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs ->
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->
  (forall x y z, BFMA x y z = fp -> Binary.is_finite _ _ fp = true /\
      Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov) ->      
  Binary.is_finite (fprec t) (femax t) fp = true /\
  Rabs (FT2R fp - rp) <=  error_rel t (length v1  + 1) rp_abs.
Proof.
intros t v1 v2 Hlen.
replace (combine (map FT2R v1) (map FT2R v2)) with (map FR2 (combine v1 v2)) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).
rewrite <- H. clear H; revert Hlen.
induction (List.combine v1 v2).
{
intros Hlen fp rp rp_abs ? Hfp Hrp Hrpa Hin Hfin.
inversion Hrp.
inversion Hfp.
inversion Hrpa.
subst; split; [simpl; auto|].  
unfold error_rel.
rewrite Zaux.Zle_bool_true; try lia.
simpl.
rewrite Rminus_eq_0;
rewrite Rabs_R0;
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros Hlen fp rp rp_abs ? Hfp Hrp Hrpa Hin Hfin.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
assert (HFIN: Binary.is_finite (fprec t) (femax t) fp = true).
  { inversion Hfp. specialize (Hfin (fst a) (snd a) s H0);
      destruct Hfin as (A & B); subst; auto. }
split; auto.
rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof 
  is_finite_fma_no_overflow t (BFMA (fst a) (snd a) neg_zero) 
    (fst a) (snd a) neg_zero HFIN eq_refl as Hov.
assert ( HFINa: 
      (Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true).
  { split. apply Hin; simpl; auto. simpl; auto. } destruct HFINa as (A & C).
  destruct A as (A & B).
pose proof fma_accurate t (fst a) A (snd a) B neg_zero C Hov as Hacc; clear Hov A B C.
destruct Hacc as (e & d & He & Hd & A). rewrite A; clear A.
unfold error_rel; simpl.
inversion Hrpa. inversion H3; subst.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + default_rel t - 1) with (default_rel t) by nra.
field_simplify_Rabs. unfold FR2, Rabsp. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
rewrite Rmult_plus_distr_l. rewrite Rmult_comm.
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0))) with
  (Rabs (FT2R f) * Rabs (FT2R f0)).
apply Rplus_le_compat. 
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rle_refl;
  try apply Rabs_pos; auto; apply Rmult_le_pos; try apply Rabs_pos.
  field_simplify; auto; try apply default_rel_sep_0.
symmetry. rewrite Rabs_pos_eq; auto.
  apply Rmult_le_pos; try apply Rabs_pos.
unfold FR2 in *. simpl in Hrp; auto.
}
(* non-empty l *)
intros; inversion Hfp.
inversion Hrp. 
inversion Hrpa. 
clear H0 H2 H4 H6 H8 H10 l0 l1 l2 xy xy1 xy0. 
assert (HFINa: 
        Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) by (apply Hin; simpl; auto).
(* IHl *)
assert (Hinl:forall xy : ftype t * ftype t,
       In xy l ->
       Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
       Binary.is_finite (fprec t) (femax t) (snd xy) = true).
{ intros; apply Hin; simpl; auto. }
clear Hin.
specialize (Hfin (fst a) (snd a) s H1).
destruct Hfin as (HFINfp & HOVfp).
assert (H0: forall x y z : ftype t,
       BFMA x y z = s ->
       Binary.is_finite (fprec t) (femax t) s = true /\
       Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov).
{ intros. subst. 
  match goal with |- context [?A /\ ?B] =>
    assert A; [ |repeat split; auto  ]
  end.
  { revert HFINa. revert HFINfp. 
    set (u :=  (BFMA x y z)).
    unfold BFMA. destruct a; simpl. 
    destruct u; destruct f; destruct f0; simpl; intros; 
        destruct HFINa; try discriminate; auto. }
  eapply is_finite_fma_no_overflow; try apply H0; auto. 
}
specialize (IHl Hlen s s0 s1 H3 H7 H11 Hinl H0). 
destruct IHl as (HFINs & IH).
match goal with |- context [?A /\ ?B] =>
  assert A; [ |repeat split; auto  ]
end.
{
unfold rounded, ov, FT2R in HOVfp.
destruct HFINa as (A & B).
pose proof (Binary.Bfma_correct (fprec t) (femax t) (fprec_gt_0 t) 
                      (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE (fst a) (snd a) s A B HFINs) as HCOR. 
apply Rlt_bool_true in HOVfp.
simpl in HCOR, HOVfp.
rewrite HOVfp in HCOR.
unfold BFMA; destruct HCOR as (_ & HFIN & _); auto.
}
destruct HFINa as (A & B).
pose proof (fma_accurate t (fst a) A (snd a) B s HFINs HOVfp) as Hplus.
destruct Hplus as (d' & e'& Hd'& He'& Hplus); rewrite Hplus; 
  clear Hplus HOVfp.
(* algebra *)
destruct a; cbv [ FR2 Rabsp fst snd].
field_simplify_Rabs.
replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0) with
  ( (FT2R f * FT2R f0 + FT2R s) * d' + (FT2R s - s0) + e') by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l; apply IH | ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_r | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_l].
  assert (Hs: Rabs(FT2R s) <= error_rel t (length l + 1) s1 + Rabs s1).
  { apply Rabs_le_minus in IH.
    eapply Rle_trans; [apply IH |apply Rplus_le_compat; try apply Rle_refl ].
    eapply sum_rel_R_Rabs. apply H7. apply H11.
  }
  apply Hs. apply Hd'.
eapply Rle_trans; 
  [apply Rplus_le_compat_l; apply He' | ].
cbv [error_rel]; rewrite !Zle_imp_le_bool.
set (D:= default_rel t).
set (E:= default_abs t).
replace (length ((f, f0) :: l) + 1 - 1)%nat with (length l + 1)%nat by (simpl; lia).
replace (length l + 1 - 1)%nat with (length l)%nat by lia.
set (n:= length l). 
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0) + s1)) with 
  (Rabs (FT2R f) * Rabs (FT2R f0) + s1).
replace (Rabs s1) with s1.  
rewrite <- Rabs_mult. 
set (F:= Rabs (FT2R f * FT2R f0)).
replace ((F + (((1 + D) ^ n - 1) * (s1 + E / D) + s1)) * D +
((1 + D) ^ n - 1) * (s1 + E / D) + E) with
((1 + D) * ((1 + D) ^ n - 1) * (s1 + E / D) + F * D + s1 * D + E) by nra.
replace ((1 + D) * ((1 + D) ^ n - 1) * (s1 + E / D) + F * D + s1 * D + E) with
(((1 + D) ^ (n + 1) - 1) * (s1 + E / D) + F * D).
rewrite Rplus_assoc.
eapply Rle_trans; [  | rewrite Rmult_plus_distr_l ]. 
  apply Rle_refl.
rewrite Rplus_comm.
apply Rplus_le_compat; try nra.
rewrite Rmult_comm.
apply Rmult_le_compat; try apply Rabs_pos; try nra.
unfold D; apply Rlt_le; apply default_rel_gt_0.
rewrite Rcomplements.Rle_minus_r.
rewrite Rplus_comm.
replace (1 + D) with ((1 + D) ^ 1) at 1 by (simpl; nra); try lia.
apply Rle_pow; try lia.
rewrite Rplus_comm;
  apply Rcomplements.Rle_minus_l; field_simplify.
unfold D; apply Rlt_le; apply default_rel_gt_0.
symmetry.
rewrite Rmult_minus_distr_l.
rewrite Rmult_1_r.
replace ((1 + D) * (1 + D) ^ n) with  ((1 + D) ^ (n+1)).
field_simplify; try nra; unfold D; try apply default_rel_sep_0.
replace (1 + D) with ((1 + D) ^ 1) at 2 by (simpl; nra).
  rewrite <- Rdef_pow_add.
  f_equal;  lia. 
(* s1 = Rabs s1 *) rewrite (R_dot_prod_rel_Rabs_eq (map FR2 l) ); auto.
symmetry. rewrite Rabs_pos_eq; auto.
apply Rplus_le_le_0_compat; auto;
  try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
(* 0 <= s1 *)
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) ); try apply Rabs_pos; auto.
simpl; lia.
(* (1 <= Z.of_nat (length l + 1))%Z *)
rewrite Nat2Z.inj_add;
simpl; apply Z.le_sub_le_add_r;
ring_simplify.
replace 0%Z with (Z.of_nat 0)%Z by lia;
apply inj_le;
apply length_not_empty_nat'; auto.
Qed.

(*
Lemma dotprod_error': 
  forall (t: type)  (v1 v2: list (ftype t)), 
  length v1 = length v2 ->
  let prods := map (uncurry Rmult) (List.combine (map FT2R v1) (map FT2R v2)) in
  let abs_prods := map (uncurry Rmult) (List.combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) in
  let ov := bpow Zaux.radix2 (femax t) in
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->
  (forall x y z, BFMA x y z = (dotprod t v1 v2) -> Binary.is_finite _ _ (dotprod t v1 v2) = true /\
      Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov) ->      
  Binary.is_finite (fprec t) (femax t) (dotprod t v1 v2) = true /\
    Rabs (FT2R (dotprod t v1 v2) - sum prods) <= error_rel t (length v1 + 1) (sum abs_prods).
Proof.
intros t v1 v2 Hlen. intros. 
pose proof fma_dot_prod_rel_fold_right t v1 v2 as HFrel.
pose proof R_dot_prod_rel_fold_right t v1 v2 as HRrel.

assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).

assert (Hlenr : length (rev v1) = length (rev v2)) by admit.
pose proof dotprod_error t (rev v1) (rev v2) Hlenr 
  (dotprod t v1 v2) (sum prods) (sum abs_prods).
replace (length (rev v1)) with (length v1) in H2.
apply H2; clear H2.








simpl in HRrel; subst prods.

replace (combine (rev v1) (rev v2)) with (rev (combine v1 v2)) in *.
replace (combine (map FT2R (rev v1)) (map FT2R (rev v2))) with
  (rev (map FR2 (combine v1 v2))) in *.
replace (combine (map Rabs (map FT2R (rev v1)))
          (map Rabs (map FT2R (rev v2)))) with
  (rev (combine (map Rabs (map FT2R v1))
          (map Rabs (map FT2R v2)))) in *.
replace (map FR2 (combine v1 v2)) with 
   (combine (map FT2R v1) (map FT2R v2)) in *.
specialize (H2 HFrel HRrel).

 simpl. 
replace (map (uncurry Rmult) (combine (map FT2R v1) (map FT2R v2))) with
  (map (uncurry Rmult) (map FR2 (combine v1 v2))) by
  (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
pose proof (R_dot_prod_rel_fold_right t v1 v2).

pose proof dotprod_error t v1 v2 Hlen.
pose proof R_dot_prod_rel_fold_right t v1 v2.

*)

End NAN.

