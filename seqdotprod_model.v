Require Import vcfloat.VCFloat.
Require Import List.

(* we use -0 in order to make use of the following property of fp arithmetic
  for finite x: (x + (-0) = x) *) 
Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.

Definition dotprod {NAN: Nans} (t: type) (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2) neg_zero.
