import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem PositivityTheory.Xgn.finite_nonvanishing_selection : ∀ (σ : Type) [Finite σ] (F : Set (MvPolynomial σ ℤ)), ∃ T : Finset (MvPolynomial σ ℤ), (T : Set (MvPolynomial σ ℤ)) ⊆ F ∧ ∀ z : σ → ℂ, (∃ s ∈ F, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0) → ∃ s ∈ T, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro σ _ F
  have hfg : (Submodule.span (MvPolynomial σ ℤ) F).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTF, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset F).1 hfg
  refine ⟨T, hTF, fun z hz => ?_⟩
  obtain ⟨s, hsF, hs⟩ := hz
  by_contra hall
  push_neg at hall
  let φ : MvPolynomial σ ℤ →+* ℂ := (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : Ideal.span (T : Set (MvPolynomial σ ℤ)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro t ht
    exact RingHom.mem_ker.2 (hall t ht)
  have hsT : s ∈ Submodule.span (MvPolynomial σ ℤ) (T : Set (MvPolynomial σ ℤ)) := by
    rw [← hT]
    exact Submodule.subset_span hsF
  exact hs (RingHom.mem_ker.1 (hle hsT))
