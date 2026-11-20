import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af Formalism.ConjugateSelfDual UpperTheory.V.Base

/- English proof (translation)
Unfold `UpperTheory.V.Af.Tw.ResOpen`. Introduce `F L Ω _ _ _ _ _ _ _ _ _ _ _`. Establish `hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω` using `rfl`. Take `⟨hemb, hop, hidx⟩` from `UpperTheory.V.Base.galEmbTop F L Ω`. Rewrite using `[hre]`.

Use `⟨⟨hemb, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]`. Conclude with `hop`. Rewrite using `[UpperTheory.V.Base.range_galEmb]`. Conclude with `hidx`.
-/
theorem UpperTheory.V.Af.Tw.resOpen :
    UpperTheory.V.Af.Tw.ResOpen := by
  unfold UpperTheory.V.Af.Tw.ResOpen
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _
  have hre : resG F L Ω = UpperTheory.V.Base.galEmb F L Ω := rfl
  obtain ⟨hemb, hop, hidx⟩ := UpperTheory.V.Base.galEmbTop F L Ω
  rw [hre]
  refine ⟨⟨hemb, ?_⟩, ?_⟩
  · rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hop
  · rw [UpperTheory.V.Base.range_galEmb]
    exact hidx
