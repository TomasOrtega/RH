import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) =
      ∑ j ∈ Finset.range k,
        (X (Sum.inl (e a)) : MvPolynomial (σ ⊕ σ) ℝ) ^ j * X (Sum.inr (e a)) ^ (k - 1 - j) := by
  simp [psumExpansion, map_sum, map_mul, map_pow, rename_X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem isHomogeneous_rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    (rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))).IsHomogeneous
      (k - 1) := by
  rw [rename_map_psumExpansion]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j + (k - 1 - j) = k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have h := ((isHomogeneous_X ℝ (Sum.inl (e a) : σ ⊕ σ)).pow j).mul
    ((isHomogeneous_X ℝ (Sum.inr (e a) : σ ⊕ σ)).pow (k - 1 - j))
  simpa [hj'] using h

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem mixDiff_sum_pow {σ : Type} [Fintype σ] (r k : ℕ) (e : Fin r → σ) :
    mixDiff (∑ a, X (e a) ^ k : MvPolynomial σ ℝ) =
      ∑ a, (X (Sum.inl (e a)) - X (Sum.inr (e a))) *
        rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) := by
  unfold mixDiff
  simp only [map_sum, map_pow, rename_X, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rename_map_psumExpansion, mul_comm, (Commute.all _ _).geom_sum₂_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMixExpansion_psum_mul : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  intro σ _ _ r k m e G hG
  refine ⟨?_, fun i => ?_⟩
  · rw [mixDiff_sum_pow, ← Finset.sum_fiberwise Finset.univ e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  · exact (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_rename_map_psumExpansion r k e a).mul hG

end GlobalTheory.CompanionTheory.Ar.Num
