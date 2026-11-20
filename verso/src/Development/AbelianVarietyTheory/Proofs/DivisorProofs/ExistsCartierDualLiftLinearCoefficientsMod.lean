import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
