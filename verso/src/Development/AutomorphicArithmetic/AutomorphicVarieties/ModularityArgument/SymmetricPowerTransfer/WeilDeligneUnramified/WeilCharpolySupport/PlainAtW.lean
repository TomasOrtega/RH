import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowOfRealInjective

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

/- English proof (translation)
Introduce `e`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at e`. Conclude with `h1 e`. Conclude with `h2 e`. Conclude with `h4 (by rw [pow_two]; nth_rewrite 1 [e]; simp)`.

Conclude with `h3 (eq_inv_of_mul_eq_one_left e.symm)`. Conclude with `h1 e.symm`. Conclude with `h2 (inv_mul_eq_one.mp e.symm)`. Establish `e' : a ^ 2 * p = 1` using `by rw [pow_two, mul_assoc, ← e]; simp`. Conclude with `h5 (eq_inv_of_mul_eq_one_left e')`.

Conclude with `h3 (by simpa using congrArg (·⁻¹) e)`. Conclude with `h1 e`.
-/
private theorem ratios {G : Type*} [CommGroup G] (a p : G) (h1 : p ≠ 1) (h2 : a ≠ p) (h3 : a ≠ p⁻¹)
    (h4 : a ^ 2 ≠ p) (h5 : a ^ 2 ≠ p⁻¹) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ (![a, 1, a⁻¹] : Fin 3 → G) j * p := by
  intro e
  fin_cases i <;> fin_cases j <;> simp at e
  · exact h1 e
  · exact h2 e
  · exact h4 (by rw [pow_two]; nth_rewrite 1 [e]; simp)
  · exact h3 (eq_inv_of_mul_eq_one_left e.symm)
  · exact h1 e.symm
  · exact h2 (inv_mul_eq_one.mp e.symm)
  · have e' : a ^ 2 * p = 1 := by rw [pow_two, mul_assoc, ← e]; simp
    exact h5 (eq_inv_of_mul_eq_one_left e')
  · exact h3 (by simpa using congrArg (·⁻¹) e)
  · exact h1 e

/- English proof (translation)
Introduce `h`. Establish `e : absPow k ((1 : ℝ) : ℂ) = absPow k ((0 : ℝ) : ℂ)`. Simplify `h` using `[absPow_zero]`. Conclude with `one_ne_zero (GlobalTheory.TypeTwo.absPow_ofReal_injective k _ _ e)`.
-/
private theorem absOne_ne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro h
  have e : absPow k ((1 : ℝ) : ℂ) = absPow k ((0 : ℝ) : ℂ) := by
    simpa [absPow_zero] using h
  exact one_ne_zero (GlobalTheory.TypeTwo.absPow_ofReal_injective k _ _ e)

end UpperTheory.V.Z.Sym.W

/- English proof (translation)
Introduce `hL L _ _ _ σ π hσ hl w hw a ha ⟨hs, τ₀, h₀, hq⟩ τ hτ`. Establish `hc` using `hl.comp w hw τ hτ`. Take `⟨e⟩` from `UpperTheory.building_component_uniqueness L 3 σ hσ w hw _ _ _ _ h₀ hc`. Establish `hq' : IsSubquotient τ.ρ (prinSeries ![a, 1, a⁻¹])` using `(IsSubquotient.of_surjective e.toIntertwiningMap e.surjective).trans hq`. Establish `hp` using `absOne_ne (Kw w)`.

Establish `n1` using `ha 1 (Or.inl rfl) 1 (Or.inl rfl)`. Establish `n2` using `ha 1 (Or.inl rfl) (-1) (Or.inr rfl)`. Establish `n3` using `ha 2 (Or.inr rfl) 1 (Or.inl rfl)`. Establish `n4` using `ha 2 (Or.inr rfl) (-1) (Or.inr rfl)`. Simplify using `only [pow_one, Int.cast_one, Int.cast_neg, absPow_neg] at n1 n2 n3 n4`.

Conclude with `UpperTheory.V.Z.Sym.W.plainOf hL L 3 w τ _ hs hq' (ratios a _ hp n1 n2 n3 n4)`.
-/
theorem UpperTheory.V.Z.Sym.W.plainAtW :
    UpperTheory.V.Z.Sym.W.PlainAtW := by
  intro hL L _ _ _ σ π hσ hl w hw a ha ⟨hs, τ₀, h₀, hq⟩ τ hτ
  have hc := hl.comp w hw τ hτ
  obtain ⟨e⟩ := UpperTheory.building_component_uniqueness L 3 σ hσ w hw _ _ _ _ h₀ hc
  have hq' : IsSubquotient τ.ρ (prinSeries ![a, 1, a⁻¹]) :=
    (IsSubquotient.of_surjective e.toIntertwiningMap e.surjective).trans hq
  have hp := absOne_ne (Kw w)
  have n1 := ha 1 (Or.inl rfl) 1 (Or.inl rfl)
  have n2 := ha 1 (Or.inl rfl) (-1) (Or.inr rfl)
  have n3 := ha 2 (Or.inr rfl) 1 (Or.inl rfl)
  have n4 := ha 2 (Or.inr rfl) (-1) (Or.inr rfl)
  simp only [pow_one, Int.cast_one, Int.cast_neg, absPow_neg] at n1 n2 n3 n4
  exact UpperTheory.V.Z.Sym.W.plainOf hL L 3 w τ _ hs hq' (ratios a _ hp n1 n2 n3 n4)
