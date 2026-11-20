import Mathlib
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
open Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.AbsIrrMap

/- English proof (translation)
Introduce `K K' G _ _ _ _ _ _ φ χ h`. Take `⟨n, ρ, hi, hρ⟩` from `h`. Set `A` to `AlgebraicClosure K`. Set `A'` to `AlgebraicClosure K'`. Use `letI : Algebra K A' := ((algebraMap K' A').comp φ).toAlgebra`.

Set `ψ : A →ₐ[K] A'` to `IsAlgClosed.lift`. Establish `hψ : ∀ x : K, ψ (algebraMap K A x) = algebraMap K' A' (φ x)` using `fun x => by`. Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression. Set `ρ' : Representation A' G (Fin n → A')` to `GlobalTheory.BrauerRealise.mapScalars (ψ : A →+* A') ρ`.

Establish `hch : ∀ g, ρ'.character g = ψ (ρ.character g)` using `GlobalTheory.BrauerRealise.character_mapScalars (ψ : A →+* A') ρ`. Use `⟨n, ρ', GlobalTheory.BrauerRealise.isIrreducible_of_sum_char_mul_char_inv ρ' ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `: Invertible ((Nat.card G : ℕ) : A)` using `invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Establish `hcard : ((Nat.card G : ℕ) : A) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `ho` using `Representation.char_orthonormal ρ ρ`.

Rewrite `ho` using `[if_pos ⟨Representation.Equiv.refl ρ⟩]`. Establish `hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : A)`. Clear denominators, using `at ho` for the nonvanishing conditions. Simplify using `using ho`. Simplify using `only [hch, ← map_mul, ← map_sum, hsum]`.

Conclude with `map_natCast ψ _`. Rewrite using `[hch, hρ, hψ]`.
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
