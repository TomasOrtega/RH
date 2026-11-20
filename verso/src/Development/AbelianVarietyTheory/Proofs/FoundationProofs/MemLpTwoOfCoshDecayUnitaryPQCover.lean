import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod pOf)
open GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix

namespace GlobalTheory.CoshSqInt

variable {p q : ℕ}

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0`. Rewrite using `[(pOf_herm B).eq]`. Simplify using `[pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]`. Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]`.
-/
theorem pOf_mem_pR (B : Matrix (Fin p) (Fin q) ℂ) : pOf B ∈ pR p q := by
  refine ⟨?_, ?_⟩
  · change (pOf B)ᴴ * Jm p q + Jm p q * pOf B = 0
    rw [(pOf_herm B).eq]
    simp [pOf, Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  · rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp [pOf]

/- English proof (translation)
Use `set B := cartanB (T.covU g) with hB`. Use `⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩` and prove the remaining obligations. Take `⟨k₁, -, k₂, -, h⟩` from `isCartan_cartanB (T.covU g)`. Establish `h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q)`. Rewrite using `[T.expt_cov _ (pOf_mem_pR B).1]`.

Conclude with `h`. Establish `h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂`. Rewrite using `[map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `IsKC _`. Rewrite using `[h2]`.

Apply the tactic sequence `rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp`.
-/
theorem exists_cartan (T : GrpData p q) (g : T.G) :
    ∃ k ∈ T.Kset, g = k * T.expt (pOf (cartanB (T.covU g))) := by
  set B := cartanB (T.covU g) with hB
  refine ⟨g * (T.expt (pOf B))⁻¹, ?_, by simp⟩
  obtain ⟨k₁, -, k₂, -, h⟩ := isCartan_cartanB (T.covU g)
  have h1 : ((T.cov g : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.fromBlocks k₁ 0 0 k₂ * ((T.cov (T.expt (pOf B)) : GL (Ix p q) ℂ) : Mat p q) := by
    rw [T.expt_cov _ (pOf_mem_pR B).1]; exact h
  have h2 : ((T.cov (g * (T.expt (pOf B))⁻¹) : GL (Ix p q) ℂ) : Mat p q) = Matrix.fromBlocks k₁ 0 0 k₂ := by
    rw [map_mul, map_inv, Units.val_mul, h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  change IsKC _
  rw [h2]
  rintro (a | a) (b | b) h <;> simp [sameBlock] at h <;> simp

/- English proof (translation)
Unfold `decay coshPow singVal`. Rewrite using `[← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: (pOf (cartanB g)).toBlocks₁₂ = cartanB g` using `by simp [pOf]`. Rewrite using `[this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]`.

Use `congr 1`. Rewrite using `[← Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem decay_sq (n : ℕ) (g : Formalism.BasicNotions.UpqT p q) :
    decay n (pOf (cartanB g)) ^ 2 = coshPow (2 * (n : ℝ)) g := by
  unfold decay coshPow singVal
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (pOf (cartanB g)).toBlocks₁₂ = cartanB g := by simp [pOf]
  rw [this, Real.rpow_neg (Real.cosh_pos _).le, inv_pow, ← pow_mul, mul_comm n 2]
  congr 1
  rw [← Real.rpow_natCast]; push_cast; rfl

/- English proof (translation)
Introduce `hI p q n hn T f C hf hd`. Take `⟨m, hm⟩` from `GlobalTheory.MinfMeasure.exists_isMinf p q`. Establish `hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ)`. Establish `: ((p + q : ℕ) : ℝ) < n` using `by exact_mod_cast hn`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `hI.1 p q m hm _ hc`. Use `haveI := hm.1`. Use `haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T`. Use `haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩`. Take `⟨t, ht⟩` from `GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m`.

Establish `h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU)`. Rewrite using `[ht]`. Conclude with `h1.smul_measure_nnreal`. Establish `h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar` using `h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable`. Establish `hfm : AEStronglyMeasurable f T.haar` using `hf.measurable.aestronglyMeasurable`.

Rewrite using `[memLp_two_iff_integrable_sq_norm hfm]`. Use `(h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Take `⟨k, hk, hg⟩` from `exists_cartan T g`. Establish `h4` using `hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))`. Rewrite `h4` using `[← hg]`.

Rewrite using `[Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) h4 2`.
-/
theorem memLp_two_of_decay : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n →
    ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f →
    (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  intro hI p q n hn T f C hf hd
  obtain ⟨m, hm⟩ := GlobalTheory.MinfMeasure.exists_isMinf p q
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * (n : ℝ) := by
    have : ((p + q : ℕ) : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := hI.1 p q m hm _ hc
  haveI := hm.1
  haveI := GlobalTheory.DetSqrtCover.isHaarMeasure_map_covU T
  haveI : BorelSpace (Formalism.BasicNotions.UpqT p q) := ⟨rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul (T.haar.map T.covU) m
  have h2 : Integrable (coshPow (2 * (n : ℝ))) (T.haar.map T.covU) := by
    rw [ht]; exact h1.smul_measure_nnreal
  have h3 : Integrable (coshPow (2 * (n : ℝ)) ∘ T.covU) T.haar :=
    h2.comp_measurable (GlobalTheory.DetSqrtCover.continuous_covU T).measurable
  have hfm : AEStronglyMeasurable f T.haar := hf.measurable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hfm]
  refine (h3.const_mul (C ^ 2)).mono' (hfm.norm.pow 2) (Filter.Eventually.of_forall fun g => ?_)
  obtain ⟨k, hk, hg⟩ := exists_cartan T g
  have h4 := hd k hk _ (pOf_mem_pR (cartanB (T.covU g)))
  rw [← hg] at h4
  rw [Real.norm_of_nonneg (by positivity), Function.comp_apply, ← decay_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h4 2

end GlobalTheory.CoshSqInt
