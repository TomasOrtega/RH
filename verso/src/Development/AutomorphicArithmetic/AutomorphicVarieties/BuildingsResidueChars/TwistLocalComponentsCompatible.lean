import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.LocGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `E _ _ _ a P t w ρ hρ`. Use `⟨_, hρ.twist (GlobalTheory.HeckeGal.Model.absPow E t), ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.LocGL.IrrGL.tw_of ρ.ρ ρ.smooth ρ.irred _ (isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E t) w)).symm.trans ?_` and prove the remaining obligations. Unfold `GlobalTheory.LocGL.IrrGL.nu`. Use `congr 1`.

Conclude with `GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E t) w`.
-/
theorem UpperTheory.twist_local_components_compatible :
    TwistLoc := by
  intro E _ _ _ a P t w ρ hρ
  refine ⟨_, hρ.twist (GlobalTheory.HeckeGal.Model.absPow E t), ?_⟩
  refine (GlobalTheory.LocGL.IrrGL.tw_of ρ.ρ ρ.smooth ρ.irred _
    (isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E t) w)).symm.trans ?_
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E t) w
