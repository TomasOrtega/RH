import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ne_zero_of_finprod_mem_ne_zero {α : Type} (f : α → ℂ) (S : Set α) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ w ∈ S, f w ≠ 0) : ∀ w ∈ S, f w ≠ 0 := by
  intro w hw h0
  have hfin : (S ∩ Function.mulSupport f).Finite := hf.subset Set.inter_subset_right
  apply h
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq f (t := hfin.toFinset) (by
    ext x; simp only [Set.mem_inter_iff, Set.Finite.coe_toFinset]; tauto)]
  exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem exists_support_of_stTw2_ne_zero (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y, φ y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂ := by
  obtain ⟨δ, ⟨hδ₁, hδ₂⟩, x, hx⟩ := exists_ne_zero_of_clSum_ne_zero _ _ _ _ _ h
  refine ⟨_, hx, ?_, ?_⟩
  · change (nrmL a w (x.1⁻¹ * δ.1 * thL a w x.1)).val.charpoly = Q₁
    rw [nrmL_twConj, ← hδ₁, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  · change (nrmL b w (x.2⁻¹ * δ.2 * thL b w x.2)).val.charpoly = Q₂
    rw [nrmL_twConj, ← hδ₂, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.BCT.GeoFin

namespace GlobalTheory.BCT.GeoFin

end GlobalTheory.BCT.GeoFin
