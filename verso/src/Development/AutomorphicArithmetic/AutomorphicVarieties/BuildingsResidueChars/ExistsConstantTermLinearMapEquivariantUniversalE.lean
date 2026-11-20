import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `K _ _ n r`. Establish `h` using `fun φ : automorphicForms K n => UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2`. Use `choose hs hX using h`. Set `f : automorphicForms K n →ₗ[ℂ] archSmooth K n` to `{ toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩ map_add' := fun φ ψ => Subtype.ext (funext fun g => constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g) map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }`. Use `⟨f, fun _ => rfl, fun u => ?_⟩` and prove the remaining obligations.

Proceed by induction on `u using UEnv.induction with`. Consider the case `halg c`. Introduce `φ`. Establish `e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ` using `Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)`. Rewrite using `[e, map_smul]`.

Conclude with `Subtype.ext (coe_uAction_algebraMap c (f φ)).symm`. Consider the case `hι X => exact fun φ => Subtype.ext (hX φ X).symm`. Consider the case `hmul a b ha hb`. Introduce `φ`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]`.

Consider the case `hadd a b ha hb`. Introduce `φ`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]`.
-/
theorem UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), ∃ f : automorphicForms K n →ₗ[ℂ] archSmooth K n, (∀ φ, (f φ).1 = constantTerm r φ.1) ∧ ∀ u φ, f (uActionAF K n u φ) = uAction u (f φ) := by
  intro K _ _ n r
  have h := fun φ : automorphicForms K n =>
    UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2
  choose hs hX using h
  let f : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
    { toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩
      map_add' := fun φ ψ => Subtype.ext (funext fun g =>
        constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g)
      map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }
  refine ⟨f, fun _ => rfl, fun u => ?_⟩
  induction u using UEnv.induction with
  | halg c =>
    intro φ
    have e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ :=
      Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)
    rw [e, map_smul]
    exact Subtype.ext (coe_uAction_algebraMap c (f φ)).symm
  | hι X => exact fun φ => Subtype.ext (hX φ X).symm
  | hmul a b ha hb =>
    intro φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb =>
    intro φ
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]
