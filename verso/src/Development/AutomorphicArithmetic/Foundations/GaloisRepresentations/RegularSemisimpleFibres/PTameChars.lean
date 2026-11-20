import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π ω h`. Take `⟨μ, hμ, H⟩` from `h`. Establish `hs : ∀ j, IsSmoothChar (μ j)` using `fun j => isSmoothChar_of_isTame (hμ j).isTame`. Use `⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩` and prove the remaining obligations. Conclude with `(hμ j).isTame u hu`.

Use `hasSupport_of_isCuspSupport H` as an intermediate fact. Conclude with `this`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.tameChars :
    TameChars := by
  intro k _ _ _ _ N V _ _ π ω h
  obtain ⟨μ, hμ, H⟩ := h
  have hs : ∀ j, IsSmoothChar (μ j) := fun j => isSmoothChar_of_isTame (hμ j).isTame
  refine ⟨μ, hs, fun j u hu => ?_, ?_, fun j u => hμ j u⟩
  · exact (hμ j).isTame u hu
  · have := hasSupport_of_isCuspSupport H
    exact this
