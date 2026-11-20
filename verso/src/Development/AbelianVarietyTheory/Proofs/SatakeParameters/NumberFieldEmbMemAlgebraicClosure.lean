import Mathlib

namespace GlobalTheory

open IntermediateField

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff]`. Establish `hz : IsAlgebraic ℚ z` using `Algebra.IsAlgebraic.isAlgebraic z`. Simplify using `using hz.algHom e.toRatAlgHom`.
-/
theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

/- English proof (translation)
Set `e' : LL →+* algebraicClosure ℚ ℂ` to `(e.codRestrict (algebraicClosure ℚ ℂ).toSubring (fun z => numberField_emb_mem_algebraicClosure e z))`. Use `letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra`. Use `letI : Algebra LL ℂ_[p] := i.toAlgebra`. Use `haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) := IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)`. Use `haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ`.

Use `haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) LL`. Set `lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p]` to `IsAlgClosed.lift`. Use `⟨lamA.toRingHom, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z` using `rfl`. Rewrite using `[h1]`.

Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := IsAlgClosed.lift
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
