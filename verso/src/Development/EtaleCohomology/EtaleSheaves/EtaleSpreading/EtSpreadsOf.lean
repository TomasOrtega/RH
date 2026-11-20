import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreads

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf.Cut

def FP : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.FinitePresentation

def FPSpreads : Prop := MorphismProperty.PreIndSpreads.{0} FP

def EtStage : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
  (_ : IsColimit c) (j : J) {T' T : CommRingCat.{0}} (f' : D.obj j ⟶ T') (f : c.pt ⟶ T) (g : T' ⟶ T),
  FP f' → IsPushout (c.ι.app j) f' f g → Et f →
  ∃ (k : J) (T'' : CommRingCat.{0}) (f'' : D.obj k ⟶ T'') (g'' : T'' ⟶ T),
    IsPushout (c.ι.app k) f'' f g'' ∧ Et f''

/- English proof (translation)
Establish `hfp : FP f`. Express the relevant statement in the definitionally equal form `f.hom.FinitePresentation`. Set `` to `f.hom.toAlgebra`. Establish `h : Algebra.Etale c.pt T` using `hf`. Conclude with `h.finitePresentation`.

Take `⟨j, T', f', g, hP, hf'⟩` from `hF.exists_isPushout hc f hfp`. Conclude with `hS hc j f' f g hf' hP hf`.
-/
theorem EtSpreads_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.SpreadPf.EtSpreads where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    have hfp : FP f := by
      change f.hom.FinitePresentation
      let := f.hom.toAlgebra
      have h : Algebra.Etale c.pt T := hf
      exact h.finitePresentation
    obtain ⟨j, T', f', g, hP, hf'⟩ := hF.exists_isPushout hc f hfp
    exact hS hc j f' f g hf' hP hf

/- English proof (translation)
The claim follows from `LateralTheory.E.SpreadPf.Spread_of (EtSpreads_of hF hS)`.
-/
theorem Spread_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.DescendPf.Spread :=
  LateralTheory.E.SpreadPf.Spread_of (EtSpreads_of hF hS)

end LateralTheory.E.SpreadPf.Cut
