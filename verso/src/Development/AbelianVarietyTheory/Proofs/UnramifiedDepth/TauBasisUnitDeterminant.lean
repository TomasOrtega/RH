import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitDeterminantBasis

open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.tau_basis_unit_determinant

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by
  intro p _ OE _ _ _ O _ _ _ w t ht hsep
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  have hxM := (mem_maximalIdeal _).2 hx
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] O ⧸ maximalIdeal O) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] (maximalIdeal O)).comp (tauExt (t j))
  refine GlobalTheory.UnitDeterminantBasis.det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    rw [← Ideal.Quotient.eq]
    simpa [T, tauExt] using h1
  · intro j
    have h1 : tauExt (t j) w.e = 1 := ht j
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1

end GlobalTheory.tau_basis_unit_determinant
