import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAbsGtOne

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.PrimeSplit

open Matrix GlobalTheory.LeviLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `k l`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, Finset.sum_mul]`. Simplify using `only [hJ]`. Use `Finset.sum_comm.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem skew_gram (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (ι : Matrix (Fin n) (Fin n₁) E) :
    ∀ k l, σ ((ιᵀ * J * ι.map σ) l k) = -(ιᵀ * J * ι.map σ) k l := by
  intro k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, Finset.sum_mul]
  simp only [hJ]
  refine Finset.sum_comm.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_`. Rewrite using `[← hH.gram]`.

Conclude with `skew_gram hσ hW H'.ι`. Consider the case `succ j ih`. Introduce `hj`. Rewrite using `[← (hiso j (by omega)).2.2.2.2.2.1]`. Conclude with `skew_gram hσ (ih (by omega)) (pl j).ι`.
-/
theorem skew_sp (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {d d₁ p : ℕ} {W : Spc F E d} (hW : ∀ i j, σ (W.J j i) = -W.J i j)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
    {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))} (hH : H'.IsAdapted σ B W (sp 0) i₀ i₁)
    (hiso : ∀ i < p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) :
    ∀ j ≤ p, ∀ k l, σ ((sp j).J l k) = -(sp j).J k l := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [← hH.gram]
    exact skew_gram hσ hW H'.ι
  | succ j ih =>
    intro hj
    rw [← (hiso j (by omega)).2.2.2.2.2.1]
    exact skew_gram hσ (ih (by omega)) (pl j).ι

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[lawFn, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]`.
-/
theorem norm_lawFn (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ‖lawFn χ z t‖ = (absE F E t : ℝ) ^ z := by
  rw [lawFn, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]

/- English proof (translation)
Introduce `e` and use `by have h := congrArg norm e rw [norm_lawFn, norm_lawFn] at h exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne h`.
-/
theorem lawFn_ne (α β : Chr F E) {z z' : ℝ} (hz : z < z') {t : (AE F E)ˣ} (ht : 1 < (absE F E t : ℝ)) :
    lawFn α z t ≠ lawFn β z' t := fun e => by
  have h := congrArg norm e
  rw [norm_lawFn, norm_lawFn] at h
  exact (Real.rpow_lt_rpow_of_exponent_lt ht hz).ne h

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp [mat]`.
-/
theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat]

/- English proof (translation)
Establish `e : mat (m * m') = mat m * mat m'` using `rfl`. Establish `e1 : mat (1 : UA σ W₁.J) = 1` using `rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]`.

Rewrite using `[e, Matrix.mul_assoc, h'.2.2, e1, Matrix.mul_one]`. Simplify `h.2.2` using `[e1]`.
-/
theorem isLevi_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {t s : (AE F E)ˣ}
    {m m' : UA σ W.J} (h : IsLevi (W₁ := W₁) H t 1 m) (h' : IsLevi (W₁ := W₁) H s 1 m') :
    IsLevi (W₁ := W₁) H (t * s) 1 (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (1 : UA σ W₁.J) = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h'.1, Matrix.mulVec_smul, h.1, smul_smul, Units.val_mul, mul_comm]
  · rw [e, ← Matrix.mulVec_mulVec, h'.2.1, Matrix.mulVec_smul, h.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [e, Matrix.mul_assoc, h'.2.2, e1, Matrix.mul_one]
    simpa [e1] using h.2.2

end GlobalTheory.ThK.DescB.PrimeSplit

namespace GlobalTheory.ThK.DescB.PrimeSplit

open GlobalTheory.LeviLine

end GlobalTheory.ThK.DescB.PrimeSplit

end
