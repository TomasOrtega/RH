import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

/- English proof (translation)
Introduce `F _ _ n sat inf h`. Break down `h with ⟨hC, π, rfl, rfl⟩ | ⟨hR, π, rfl, rfl⟩` into its components or cases. Conclude with `⟨.cx π, rfl, rfl⟩`. Conclude with `⟨.re π, rfl, rfl⟩`.
-/
theorem UpperTheory.CBC.SCuspOf_holds : UpperTheory.CBC.SCuspOf := by
  intro F _ _ n sat inf h
  rcases h with ⟨hC, π, rfl, rfl⟩ | ⟨hR, π, rfl, rfl⟩
  · exact ⟨.cx π, rfl, rfl⟩
  · exact ⟨.re π, rfl, rfl⟩

/- English proof (translation)
Introduce `F _ _ n π`. Consider the cases of `π with`. Consider the case `cx π => exact Or.inl ⟨inferInstance, π, rfl, rfl⟩`. Consider the case `re π => exact Or.inr ⟨inferInstance, π, rfl, rfl⟩`.
-/
theorem UpperTheory.CBC.SIsCusp_holds : UpperTheory.CBC.SIsCusp := by
  intro F _ _ n π
  cases π with
  | cx π => exact Or.inl ⟨inferInstance, π, rfl, rfl⟩
  | re π => exact Or.inr ⟨inferInstance, π, rfl, rfl⟩

/- English proof (translation)
Introduce `F _ _ n π v B B' h h'`. Consider the cases of `π with`. Consider the case `cx π => exact CG.HasSat.unique (π := CG.mk π) (w := v) h h'`. Consider the case `re π => exact UpperTheory.V.TR.CuspSub.HasSat.unique (π := π) (w := v) h h'`.
-/
theorem UpperTheory.CBC.SSatUniq_holds : UpperTheory.CBC.SSatUniq := by
  intro F _ _ n π v B B' h h'
  cases π with
  | cx π => exact CG.HasSat.unique (π := CG.mk π) (w := v) h h'
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.unique (π := π) (w := v) h h'
