import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.AbsIrrMap

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Equip the data with the indicated structure.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAbsIrrChar_map : ∀ {K K' G : Type} [Field K] [Field K'] [CharZero K] [CharZero K'] [Group G] [Fintype G]
    (φ : K →+* K') (χ : G → K), IsAbsIrrChar χ → IsAbsIrrChar (fun g => φ (χ g)) := by
  intro K K' G _ _ _ _ _ _ φ χ h
  classical
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let A := AlgebraicClosure K
  let A' := AlgebraicClosure K'
  letI : Algebra K A' := ((algebraMap K' A').comp φ).toAlgebra
  let ψ : A →ₐ[K] A' := IsAlgClosed.lift
  have hψ : ∀ x : K, ψ (algebraMap K A x) = algebraMap K' A' (φ x) := fun x => by
    rw [AlgHom.commutes]; rfl
  let ρ' : Representation A' G (Fin n → A') := GlobalTheory.BrauerRealise.mapScalars (ψ : A →+* A') ρ
  have hch : ∀ g, ρ'.character g = ψ (ρ.character g) :=
    GlobalTheory.BrauerRealise.character_mapScalars (ψ : A →+* A') ρ
  refine ⟨n, ρ', GlobalTheory.BrauerRealise.isIrreducible_of_sum_char_mul_char_inv ρ' ?_, fun t => ?_⟩
  · have : Invertible ((Nat.card G : ℕ) : A) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have hcard : ((Nat.card G : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : A) := by
      field_simp at ho
      simpa using ho
    simp only [hch, ← map_mul, ← map_sum, hsum]
    exact map_natCast ψ _
  · rw [hch, hρ, hψ]

end GlobalTheory.AbsIrrMap
