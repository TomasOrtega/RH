import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def inLH {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * H + H * X = 0

section Basic

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv hH.2`.
-/
lemma ana_inv (hH : HInvol H) : H⁻¹ = H := Matrix.inv_eq_left_inv hH.2

/- English proof (translation)
The claim follows from `IsUnit.of_mul_eq_one _ hH.2`.
-/
lemma ana_isUnit (hH : HInvol H) : IsUnit H := IsUnit.of_mul_eq_one _ hH.2

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, hH.2, Matrix.one_mul]`.
-/
lemma ana_HH_left (hH : HInvol H) (A : Matrix (Fin n) (Fin n) ℂ) : H * (H * A) = A := by
  rw [← Matrix.mul_assoc, hH.2, Matrix.one_mul]

/- English proof (translation)
Unfold `inUH at *`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma ana_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

/- English proof (translation)
Establish `hY' : Yᴴ * H = -(H * Y)` using `eq_neg_of_add_eq_zero_left hY`. Establish `hYh : Yᴴ = H * (-Y) * H⁻¹`. Rewrite using `[ana_inv hH, Matrix.mul_neg, ← hY', Matrix.mul_assoc, hH.2, Matrix.mul_one]`. Establish `hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H`. Rewrite using `[← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ (ana_isUnit hH), ana_inv hH]`.

Establish `hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]`. Unfold `inUH`. Rewrite using `[hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH.2, Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]`.
-/
lemma ana_exp (hH : HInvol H) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inLH H Y) :
    inUH H (NormedSpace.exp Y) := by
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
    rw [ana_inv hH, Matrix.mul_neg, ← hY', Matrix.mul_assoc, hH.2, Matrix.mul_one]
  have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
    rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ (ana_isUnit hH), ana_inv hH]
  have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  unfold inUH
  rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH.2, Matrix.mul_one, Matrix.mul_assoc, hc,
    Matrix.mul_one]

/- English proof (translation)
Unfold `inLH at *`. Rewrite using `[Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]`.
-/
lemma ana_rsmul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (r : ℝ) : inLH H ((r : ℂ) • X) := by
  unfold inLH at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

/- English proof (translation)
The claim follows from `ana_exp hH (ana_rsmul hX t)`.
-/
lemma ana_expt (hH : HInvol H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := ana_exp hH (ana_rsmul hX t)

/- English proof (translation)
Unfold `inLH at *`. Rewrite using `[conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma ana_add {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A + B) := by
  unfold inLH at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * H + Bᴴ * H + (H * A + H * B) = (Aᴴ * H + H * A) + (Bᴴ * H + H * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

/- English proof (translation)
Unfold `inLH at *`. Rewrite using `[conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]`.
-/
lemma ana_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) : inLH H (-A) := by
  unfold inLH at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `ana_add hA (ana_neg hB)`.
-/
lemma ana_sub {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inLH H A) (hB : inLH H B) : inLH H (A - B) := by
  rw [sub_eq_add_neg]; exact ana_add hA (ana_neg hB)

/- English proof (translation)
Unfold `inLH at *`. Establish `hX' : Xᴴ * H = -(H * X)` using `eq_neg_of_add_eq_zero_left hX`. Establish `hY' : Yᴴ * H = -(H * Y)` using `eq_neg_of_add_eq_zero_left hY`. Establish `e1 : Yᴴ * Xᴴ * H = H * Y * X`. Rewrite using `[Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]`.

Establish `e2 : Xᴴ * Yᴴ * H = H * X * Y`. Rewrite using `[Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]`. Rewrite using `[conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
lemma ana_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inLH H X) (hY : inLH H Y) :
    inLH H (X * Y - Y * X) := by
  unfold inLH at *
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * H = H * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * H = H * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

/- English proof (translation)
Establish `hX' : Xᴴ * H = -(H * X)` using `eq_neg_of_add_eq_zero_left hX`. Rewrite using `[Matrix.mul_assoc, hX', Matrix.mul_neg, ana_HH_left hH]`.
-/
lemma ana_HXH {X : Matrix (Fin n) (Fin n) ℂ} (hH : HInvol H) (hX : inLH H X) : H * Xᴴ * H = -X := by
  have hX' : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ana_HH_left hH]

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[ana_inv hH]`.
-/
lemma ana_hpart1_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z = (1 / 2 : ℂ) • (Z - H * Zᴴ * H) := by
  unfold hpart1; rw [ana_inv hH]

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[ana_inv hH]`.
-/
lemma ana_hpart2_eq (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H Z = (1 / (2 * Complex.I) : ℂ) • (Z + H * Zᴴ * H) := by
  unfold hpart2; rw [ana_inv hH]

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, hH.2, Matrix.mul_one]`.
-/
lemma ana_thetaH (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : (H * Zᴴ * H)ᴴ * H = H * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.1, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.mul_assoc, hH.2, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ana_HH_left hH]`.
-/
lemma ana_Htheta (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (H * Zᴴ * H) = Zᴴ * H := by
  rw [Matrix.mul_assoc, ana_HH_left hH]

/- English proof (translation)
Rewrite using `[ana_hpart1_eq hH, ana_hpart2_eq hH]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `inLH`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul, ana_thetaH hH, Matrix.mul_smul, Matrix.mul_sub, ana_Htheta hH, star_one_half, ← smul_add]`. Simplify using the standard rewrite rules.

Unfold `inLH`. Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul, ana_thetaH hH, Matrix.mul_smul, Matrix.mul_add, ana_Htheta hH, star_one_div_two_I, neg_smul, add_comm (H * Z), neg_add_cancel]`. Rewrite using `[smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]`. Rewrite using `[sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]`. Evaluate the numerical expressions.

Introduce `hX`. Rewrite using `[ana_HXH hH hX, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]`. Evaluate the numerical expressions.
-/
lemma ana_hpartMem (hH : HInvol H) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inLH H (hpart1 H Z) ∧ inLH H (hpart2 H Z) ∧ Z = hpart1 H Z + Complex.I • hpart2 H Z ∧
      (inLH H Z → hpart1 H Z = Z ∧ hpart2 H Z = 0) := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_sub, ana_Htheta hH, star_one_half, ← smul_add]
    simp
  · unfold inLH
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      ana_thetaH hH, Matrix.mul_smul, Matrix.mul_add, ana_Htheta hH, star_one_div_two_I, neg_smul,
      add_comm (H * Z), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    rw [ana_HXH hH hX, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

/- English proof (translation)
Establish `hZ : H * (P + Complex.I • Q)ᴴ * H = -P + Complex.I • Q`. Rewrite using `[conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ana_HXH hH hP, ana_HXH hH hQ, Complex.star_def, Complex.conj_I]`. Use `module`. Rewrite using `[ana_hpart1_eq hH, ana_hpart2_eq hH, hZ]`. Prove the components needed by the constructor for the conclusion.

Use `module`. Establish `: P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q` using `by module`. Rewrite using `[this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]`.
-/
lemma ana_hpart_unique (hH : HInvol H) {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inLH H P) (hQ : inLH H Q) :
    hpart1 H (P + Complex.I • Q) = P ∧ hpart2 H (P + Complex.I • Q) = Q := by
  have hZ : H * (P + Complex.I • Q)ᴴ * H = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, ana_HXH hH hP, ana_HXH hH hQ, Complex.star_def, Complex.conj_I]
    module
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

/- English proof (translation)
Rewrite using `[ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`. Use `module`.
-/
lemma ana_hpart1_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z - W) = hpart1 H Z - hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

/- English proof (translation)
Rewrite using `[ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`. Use `module`.
-/
lemma ana_hpart2_sub (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z - W) = hpart2 H Z - hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

/- English proof (translation)
Rewrite using `[ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`. Use `module`.
-/
lemma ana_hpart1_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (Z + W) = hpart1 H Z + hpart1 H W := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart1_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

/- English proof (translation)
Rewrite using `[ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]`. Use `module`.
-/
lemma ana_hpart2_add (hH : HInvol H) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (Z + W) = hpart2 H Z + hpart2 H W := by
  rw [ana_hpart2_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  module

/- English proof (translation)
Rewrite using `[one_div, mul_inv, Complex.inv_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ana_inv2I : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [one_div, mul_inv, Complex.inv_I]; ring

/- English proof (translation)
Rewrite using `[ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[hs]`. Apply the tactic sequence `match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq`.
-/
lemma ana_hpart1_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart1 H Z - (y : ℂ) • hpart2 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart1_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

/- English proof (translation)
Rewrite using `[ana_hpart1_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[hs]`. Apply the tactic sequence `match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq`.
-/
lemma ana_hpart2_smul (hH : HInvol H) (x y : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart2 H (((x : ℂ) + (y : ℂ) * Complex.I) • Z) = (x : ℂ) • hpart2 H Z + (y : ℂ) • hpart1 H Z := by
  rw [ana_hpart1_eq hH, ana_hpart2_eq hH, ana_hpart2_eq hH, ana_inv2I, conjTranspose_smul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hs : star ((x : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) - (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hs]
  match_scalars <;> first | ring1 | linear_combination ((y : ℂ) / 2) * Complex.I_sq | linear_combination (-(y : ℂ) / 2) * Complex.I_sq

end Basic

end AAInvW
