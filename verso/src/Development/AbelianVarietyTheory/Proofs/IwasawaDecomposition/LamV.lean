import Mathlib
import Formalism.LocalRingCardinality.DataKerI

open Formalism.BasicNotions

namespace GlobalTheory.PadicPlaceExt

/- English proof (translation)
Establish `hmem : ∀ z : L, e z ∈ algebraicClosure ℚ ℂ` using `fun z => mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom e.toRatAlgHom)`. Set `e' : L →+* algebraicClosure ℚ ℂ` to `e.codRestrict (algebraicClosure ℚ ℂ) hmem`. Set `: Algebra L (algebraicClosure ℚ ℂ)` to `e'.toAlgebra`. Set `: Algebra L ℂ_[p]` to `φ.toAlgebra`. Establish `: IsScalarTower ℚ L (algebraicClosure ℚ ℂ)` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`.

Establish `: Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ)` using `algebraicClosure.isAlgebraic ℚ ℂ`. Establish `: Algebra.IsAlgebraic L (algebraicClosure ℚ ℂ)` using `Algebra.IsAlgebraic.tower_top (K := ℚ) L`. Set `f : algebraicClosure ℚ ℂ →ₐ[L] ℂ_[p]` to `IsAlgClosed.lift`. Use `⟨f.toRingHom, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[lamV, dif_pos (hmem z)]`.

Conclude with `(f.commutes z).symm`.
-/
theorem exists_lam {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] (e : L →+* ℂ) (φ : L →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p], ∀ z : L, φ z = lamV lam (e z) := by
  have hmem : ∀ z : L, e z ∈ algebraicClosure ℚ ℂ := fun z =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom e.toRatAlgHom)
  let e' : L →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ) hmem
  let : Algebra L (algebraicClosure ℚ ℂ) := e'.toAlgebra
  let : Algebra L ℂ_[p] := φ.toAlgebra
  have : IsScalarTower ℚ L (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic L (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let f : algebraicClosure ℚ ℂ →ₐ[L] ℂ_[p] := IsAlgClosed.lift
  refine ⟨f.toRingHom, fun z => ?_⟩
  rw [lamV, dif_pos (hmem z)]
  exact (f.commutes z).symm

end GlobalTheory.PadicPlaceExt
