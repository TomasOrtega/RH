import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial

namespace PositivityTheory.Xgn.HomogeneousComponentProduct

/- English proof (translation)
Use `conv_lhs => rw [s.as_sum, Finset.sum_mul]`. Use `conv_rhs => rw [s.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Establish `hm : IsWeightedHomogeneous w (monomial d (coeff d s)) (Finsupp.weight w d)` using `isWeightedHomogeneous_monomial _ _ _ rfl`.

Distinguish the cases in `h : Finsupp.weight w d = b`. Substitute `h` using the available equality. Rewrite using `[(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]`. Rewrite using `[(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm), hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]`.
-/
theorem comp_mul {σ M R : Type*} [CommRing R] [AddCancelCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (b : M)
    (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w (b + bg) (s * g) = weightedHomogeneousComponent w b s * g := by
  conv_lhs => rw [s.as_sum, Finset.sum_mul]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hm : IsWeightedHomogeneous w (monomial d (coeff d s)) (Finsupp.weight w d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  by_cases h : Finsupp.weight w d = b
  · subst h
    rw [(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
  · rw [(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm),
      hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]

/- English proof (translation)
Rewrite using `[s.as_sum, Finset.sum_mul, map_sum]`. Use `Finset.sum_eq_zero (fun d _ => ?_)` and prove the remaining obligations. Conclude with `((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)`.
-/
theorem comp_mul_zero {σ M R : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (c : M)
    (hc : ∀ b, c ≠ b + bg) (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w c (s * g) = 0 := by
  rw [s.as_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  exact ((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)

end PositivityTheory.Xgn.HomogeneousComponentProduct

/- English proof (translation)
Introduce `K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu`. Establish `h` using `hH _ hrel (a + bf)`. Rewrite `h` using `[map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf]`. Distinguish the cases in `hb : ∃ b, a + bf = b + bg`. Take `⟨b, hb⟩` from `hb`.

Rewrite `h` using `[hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg]`. Conclude with `⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩`. Rewrite `h` using `[PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _ (fun b hb' => hb ⟨b, hb'⟩), sub_zero]`. Break down `hP.mem_or_mem h with h | h` into its components or cases. Conclude with `absurd h hu`.

Conclude with `absurd h hfP`.
-/
theorem PositivityTheory.Xgn.homogeneous_pair_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  intro K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu
  have h := hH _ hrel (a + bf)
  rw [map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf] at h
  by_cases hb : ∃ b, a + bf = b + bg
  · obtain ⟨b, hb⟩ := hb
    rw [hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg] at h
    exact ⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩
  · rw [PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _
      (fun b hb' => hb ⟨b, hb'⟩), sub_zero] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h hu
    · exact absurd h hfP
