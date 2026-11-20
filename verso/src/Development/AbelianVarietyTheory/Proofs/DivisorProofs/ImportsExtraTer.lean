import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot

namespace GlobalTheory.LiftAndFactorization

open Formalism.L2.Pj

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Conclude with `⟨0, by rw [h0, map_zero]⟩`. Apply `IsDiscreteValuationRing.exists_lift_of_le_one` to reduce the goal to its premises. Establish `hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Establish `hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0`.

Use `hx h0` as an intermediate fact. Unfold `vV valV at this`. Conclude with `neg_eq_zero.1 this`. Use `WithZero.exp_log hne` as an intermediate fact. Rewrite `this` using `[hlog, WithZero.exp_zero]`.

Conclude with `this.ge`.
-/
theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

/- English proof (translation)
Establish `key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a` using `fun a => exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))`. Use `choose f hf using key`. Establish `inj : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective _ _`. Use `⟨{ toFun := f map_one' := inj (by rw [hf, map_one, map_one]) map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul]) map_zero' := inj (by rw [hf, map_zero, map_zero]) map_add' := fun a b => inj (by rw [map_add, hf, hf, hf, map_add]) }, ?_⟩` and prove the remaining obligations. Use extensionality with `a`.

Conclude with `hf a`.
-/
theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add, hf, hf, hf, map_add]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
