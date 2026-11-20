import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

/- English proof (translation)
Introduce `Ω _ _ _ p _ A Ωl _ _ hC j hA g`. Use `haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC`. Use `letI : Algebra Ω Ωl := j.toAlgebra`. Use `haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]`.

Use `haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω`. Set `gq : Ωl ≃ₐ[ℚ] Ωl` to `AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by`. Simplify using `only [eq_ratCast, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]`. Conclude with `map_ratCast g x)`. Establish `hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x)` using `fun x => by`.

Use `AlgEquiv.restrictNormal_commutes gq Ω x` as an intermediate fact. Rewrite `this` using `[RingHom.algebraMap_toAlgebra]`. Rewrite using `[this]`. Both sides reduce to the same expression. Use `⟨gq.restrictNormal Ω, fun x => ?_, hc⟩` and prove the remaining obligations.

Rewrite using `[hA, hA, ← hc]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `GlobalTheory.K5.Basic.isInt_gal g.symm h` as an intermediate fact. Rewrite `this` using `[AlgEquiv.symm_apply_apply]`. Then use the resulting hypothesis.

Conclude with `GlobalTheory.K5.Basic.isInt_gal g`.
-/
theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
