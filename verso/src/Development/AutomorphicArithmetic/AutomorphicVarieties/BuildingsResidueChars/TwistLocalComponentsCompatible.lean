import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.LocGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
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
