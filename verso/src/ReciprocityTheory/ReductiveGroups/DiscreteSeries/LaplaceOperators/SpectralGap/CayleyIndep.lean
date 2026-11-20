import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyIndependent

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS
open Matrix

/- English proof (translation)
Introduce `k r ε lam H _ _ _ σ P₀ P h0 h1 hDS`. Use `set σ₁ : Mat k r → (H →L[ℂ] H) := fun g => σ (P₀⁻¹ * g * P₀) with hσ₁`. Establish `e0 : star P₀ * P₀ = 1` using `Matrix.mem_unitaryGroup_iff'.mp h0.2`. Establish `e0' : P₀ * star P₀ = 1` using `Matrix.mem_unitaryGroup_iff.mp h0.2`. Establish `e1 : star P * P = 1` using `Matrix.mem_unitaryGroup_iff'.mp h1.2`.

Establish `e1' : P * star P = 1` using `Matrix.mem_unitaryGroup_iff.mp h1.2`. Establish `hinv0 : P₀⁻¹ = star P₀` using `Matrix.inv_eq_left_inv e0`. Establish `hinv1 : P⁻¹ = star P` using `Matrix.inv_eq_left_inv e1`. Establish `hH0` using `h0.1.2`. Establish `hH1` using `h1.1.2`.

Establish `hJ : star P₀ * Formalism.REAL.Jm ε * P₀ = star P * Formalism.REAL.Jm ε * P`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hH0, hH1]`. Establish `hbK : P₀ * star P ∈ Formalism.REAL.Kset ε`. Use `⟨Submonoid.mul_mem _ h0.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e1)), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc P₀ _ (star P), Matrix.mul_assoc (star P * _) P (star P), e1', Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = P₀ * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P := by rw [hJ]`. Use `_ = Formalism.REAL.Jm ε * (P₀ * star P) := by`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[e0', Matrix.one_mul]`.

Establish `haK : P * star P₀ ∈ Formalism.REAL.Kset ε`. Use `⟨Submonoid.mul_mem _ h1.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e0)), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc P _ (star P₀), Matrix.mul_assoc (star P₀ * _) P₀ (star P₀), e0', Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = P * (star P * Formalism.REAL.Jm ε * P) * star P₀ := by rw [hJ]`.

Use `_ = Formalism.REAL.Jm ε * (P * star P₀) := by`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[e1', Matrix.one_mul]`. Establish `hbU` using `ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj hbK`. Establish `haU` using `ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj haK`.

Establish `hab : P * star P₀ * (P₀ * star P) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (star P₀), e0, Matrix.one_mul, e1']`. Establish `hba : P₀ * star P * (P * star P₀) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (star P), e1, Matrix.one_mul, e0']`. Establish `hfun : (fun g => σ (P⁻¹ * g * P)) = fun g => σ₁ (P₀ * star P * g * (P * star P₀))`.

Use function extensionality and compare the values at `g`. Rewrite using `[hσ₁]`. Use `congr 1`. Rewrite using `[hinv0, hinv1]`. Simplify using `only [← Matrix.mul_assoc]`.

Rewrite using `[e0, Matrix.one_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e0, Matrix.mul_one]`. Take `⟨hc, hnt, hU, hI, hS, ⟨S0, hS0⟩, hmin⟩` from `hDS`. Rewrite using `[hfun]`.

Use `⟨⟨hc, hnt, ?_, ?_, ?_, ⟨S0, ?_⟩, fun μ S hS' => hmin μ S ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.urep_conj all_goals first | assumption | exact hU`. Apply the tactic sequence `apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.irred_conj (hirr := hI) all_goals first | assumption | exact hU`. Apply the tactic sequence `apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.sqint_conj (hsq := hS) all_goals first | assumption | exact hU`. Rewrite using `[ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]`.

Conclude with `hS0`. Apply the tactic sequence `all_goals first | assumption | exact hU`. Rewrite `hS'` using `[ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]`. Conclude with `hS'`. Apply the tactic sequence `all_goals first | assumption | exact hU`.

Unfold `Formalism.MainNotions.S.lowKSub`. Use `congrArg sSup (Set.ext fun S => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]`. Apply the tactic sequence `all_goals first | assumption | exact hU`.
-/
theorem cayleyIndep : CayleyIndepStatement := by
  intro k r ε lam H _ _ _ σ P₀ P h0 h1 hDS
  set σ₁ : Mat k r → (H →L[ℂ] H) := fun g => σ (P₀⁻¹ * g * P₀) with hσ₁
  have e0 : star P₀ * P₀ = 1 := Matrix.mem_unitaryGroup_iff'.mp h0.2
  have e0' : P₀ * star P₀ = 1 := Matrix.mem_unitaryGroup_iff.mp h0.2
  have e1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp h1.2
  have e1' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp h1.2
  have hinv0 : P₀⁻¹ = star P₀ := Matrix.inv_eq_left_inv e0
  have hinv1 : P⁻¹ = star P := Matrix.inv_eq_left_inv e1
  have hH0 := h0.1.2
  have hH1 := h1.1.2
  have hJ : star P₀ * Formalism.REAL.Jm ε * P₀ = star P * Formalism.REAL.Jm ε * P := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hH0, hH1]
  have hbK : P₀ * star P ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h0.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e1)), ?_⟩
    calc P₀ * star P * Formalism.REAL.Jm ε = P₀ * (star P * Formalism.REAL.Jm ε * P) * star P := by
          rw [Matrix.mul_assoc P₀ _ (star P), Matrix.mul_assoc (star P * _) P (star P), e1', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P₀ * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P₀ * star P) := by
          simp only [← Matrix.mul_assoc]
          rw [e0', Matrix.one_mul]
  have haK : P * star P₀ ∈ Formalism.REAL.Kset ε := by
    refine ⟨Submonoid.mul_mem _ h1.2 (Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact e0)), ?_⟩
    calc P * star P₀ * Formalism.REAL.Jm ε = P * (star P₀ * Formalism.REAL.Jm ε * P₀) * star P₀ := by
          rw [Matrix.mul_assoc P _ (star P₀), Matrix.mul_assoc (star P₀ * _) P₀ (star P₀), e0', Matrix.mul_one,
            Matrix.mul_assoc]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P₀ := by rw [hJ]
      _ = Formalism.REAL.Jm ε * (P * star P₀) := by
          simp only [← Matrix.mul_assoc]
          rw [e1', Matrix.one_mul]
  have hbU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj hbK
  have haU := ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.kset_uj haK
  have hab : P * star P₀ * (P₀ * star P) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P₀), e0, Matrix.one_mul, e1']
  have hba : P₀ * star P * (P * star P₀) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star P), e1, Matrix.one_mul, e0']
  have hfun : (fun g => σ (P⁻¹ * g * P)) = fun g => σ₁ (P₀ * star P * g * (P * star P₀)) := by
    funext g
    rw [hσ₁]
    congr 1
    rw [hinv0, hinv1]
    simp only [← Matrix.mul_assoc]
    rw [e0, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [e0, Matrix.mul_one]
  obtain ⟨hc, hnt, hU, hI, hS, ⟨S0, hS0⟩, hmin⟩ := hDS
  rw [hfun]
  refine ⟨⟨hc, hnt, ?_, ?_, ?_, ⟨S0, ?_⟩, fun μ S hS' => hmin μ S ?_⟩, ?_⟩
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.urep_conj
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.irred_conj (hirr := hI)
    all_goals first | assumption | exact hU
  · apply ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.sqint_conj (hsq := hS)
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    · exact hS0
    all_goals first | assumption | exact hU
  · rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff] at hS'
    · exact hS'
    all_goals first | assumption | exact hU
  · unfold Formalism.MainNotions.S.lowKSub
    refine congrArg sSup (Set.ext fun S => ?_)
    simp only [Set.mem_setOf_eq]
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA.ktype_iff]
    all_goals first | assumption | exact hU

end ReciprocityTheory.ChartRestriction.DS.Lap
