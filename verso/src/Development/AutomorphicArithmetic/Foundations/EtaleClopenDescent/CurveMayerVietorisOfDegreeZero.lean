import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafCurveCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

/- English proof (translation)
Introduce `_ _ R _ F X U V hUV n`. Take `⟨d, hd, -⟩` from `mayerVietoris R F`. Establish `hc` using `LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV`. Use `haveI : PreservesLimitsOfShape WalkingCospan sch := by`. Unfold `sch`.

Use `infer_instance`. Establish `P` using `(isPullback_opens_inf U V).map sch`. Use `⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[(hd _ _ hc n).2.2 x]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, rfl⟩`. Use `⟨pull R P.isoPullback.hom F n c, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨_, rfl⟩`.
-/
theorem UpperTheory.Cb.curve_mayer_vietoris_of_degree_zero :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.E4.CurveCut.LeafMV := by
  intro _ _ R _ F X U V hUV n
  obtain ⟨d, hd, -⟩ := mayerVietoris R F
  have hc := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 R U V hUV
  haveI : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch; infer_instance
  have P := (isPullback_opens_inf U V).map sch
  refine ⟨(d _ _ hc n).comp (pull R P.isoPullback.inv F n), fun x => ?_⟩
  rw [(hd _ _ hc n).2.2 x]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, Iso.inv_hom_id, pull_id]
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
