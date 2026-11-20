import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitSemiAbModel

/- English proof (translation)
Introduce `V _ _ _ hV P`. Take `⟨V₁, _, _, _, f₁, fK₁, hV₁, hinj₁, -, hfin₁, hK₁, A₁, β₁, hpb₁, -, G₁, _, _, gen₁, hG₁, hgen₁⟩` from `GlobalTheory.PolSemiAbModel.exists_model V hV P`. Take `⟨hdvr, hcpl, hch⟩` from `(GlobalTheory.LN.cDvr_iff V₁).1 hV₁`. Take `⟨W, _, _, _, _, g, hcW, hgi, hginj, -, E, hE⟩` from `GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V₁ hcpl G₁ hG₁`. Establish `hj : Function.Injective ((algebraMap W (FractionRing W)).comp g)` using `(IsFractionRing.injective W (FractionRing W)).comp hginj`.

Take `⟨fK₂, hK₂'⟩ : ∃ fK₂ : FractionRing V₁ →+* FractionRing W, ∀ a, fK₂ (algebraMap V₁ (FractionRing V₁) a) = algebraMap W (FractionRing W) (g a)` from `⟨IsFractionRing.lift (A := V₁) (K := FractionRing V₁) hj, fun a => IsFractionRing.lift_algebraMap (K := FractionRing V₁) hj a⟩`. Establish `hK₂ : fK₂.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap W (FractionRing W)).comp g` using `RingHom.ext hK₂'`. Take `⟨A, β, hpb, -, hLB⟩` from `GlobalTheory.KeyFam.SameLam.exists_polPB P (fK₂.comp fK₁)`. Establish `hG : IsSemiAbelian ((Over.pullback (spMap g)).obj G₁)` using `IsSemiAbelian.pullback _ G₁ hG₁`. Use `⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g.comp f₁, fK₂.comp fK₁, hcW, RingHom.IsIntegral.trans _ _ hfin₁.to_isIntegral hgi, hginj.comp hinj₁, ?_, A, β, hpb, hLB, ?_⟩` and prove the remaining obligations.

Introduce `a`. Rewrite using `[RingHom.comp_apply, hK₁]`. Conclude with `hK₂' _`. Set `G` to `(Over.pullback (spMap g)).obj G₁`. Set `X` to `(Over.pullback (jK V₁)).obj G₁`.

Set `T` to `(Over.pullback (spMap fK₂)).obj X`. Establish `h₁` using `(isGrpPullback_pullback G (jK W)).comp (isGrpPullback_pullback G₁ (spMap g))`. Establish `hTX` using `isGrpPullback_pullback X (spMap fK₂)`. Establish `hXG` using `isGrpPullback_pullback G₁ (jK V₁)`. Establish `hsq : spMap fK₂ ≫ jK V₁ = jK W ≫ spMap g` using `by show spMap fK₂ ≫ spMap (algebraMap V₁ _) = spMap (algebraMap W _) ≫ spMap g`.

Rewrite using `[GlobalTheory.PolSemiAbModel.spMap_comp', GlobalTheory.PolSemiAbModel.spMap_comp', hK₂]`. Establish `hTG` using `(hTX.comp hXG).congr hsq rfl`. Take `⟨e₁, he₁, -⟩` from `grpPullback_iso h₁ hTG`. Establish `hXY` using `isGrpPullback_of_iso gen₁`. Establish `hTP` using `(hTX.comp (hXY.comp hpb₁)).congr (by rw [Category.id_comp, GlobalTheory.PolSemiAbModel.spMap_comp']) rfl`.

Take `⟨e₂, he₂, -⟩` from `grpPullback_iso hTP hpb`. Conclude with `⟨G, inferInstance, hG.comm, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance, E, hE⟩`.
-/
theorem exists_split_model : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (P : PolAV (Sp (FractionRing V))), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (f : V →+* W) (fK : FractionRing V →+* FractionRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ f.IsIntegral ∧ Function.Injective f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) ∧ ∃ (A : PolAV (Sp (FractionRing W))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧ LBIso A.L (P.L.pull β) ∧ ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK W)).obj G ≅ A.A), IsSemiAbelian G ∧ IsMonHom gen.hom ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj G) := by
  intro V _ _ _ hV P
  obtain ⟨V₁, _, _, _, f₁, fK₁, hV₁, hinj₁, -, hfin₁, hK₁, A₁, β₁, hpb₁, -, G₁, _, _, gen₁, hG₁, hgen₁⟩ :=
    GlobalTheory.PolSemiAbModel.exists_model V hV P
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, -, E, hE⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V₁ hcpl G₁ hG₁
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp g) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  obtain ⟨fK₂, hK₂'⟩ : ∃ fK₂ : FractionRing V₁ →+* FractionRing W,
      ∀ a, fK₂ (algebraMap V₁ (FractionRing V₁) a) = algebraMap W (FractionRing W) (g a) :=
    ⟨IsFractionRing.lift (A := V₁) (K := FractionRing V₁) hj,
      fun a => IsFractionRing.lift_algebraMap (K := FractionRing V₁) hj a⟩
  have hK₂ : fK₂.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap W (FractionRing W)).comp g :=
    RingHom.ext hK₂'
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P (fK₂.comp fK₁)
  have hG : IsSemiAbelian ((Over.pullback (spMap g)).obj G₁) := IsSemiAbelian.pullback _ G₁ hG₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g.comp f₁, fK₂.comp fK₁, hcW,
    RingHom.IsIntegral.trans _ _ hfin₁.to_isIntegral hgi, hginj.comp hinj₁, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hK₁]
    exact hK₂' _
  · let G := (Over.pullback (spMap g)).obj G₁
    let X := (Over.pullback (jK V₁)).obj G₁
    let T := (Over.pullback (spMap fK₂)).obj X
    have h₁ := (isGrpPullback_pullback G (jK W)).comp (isGrpPullback_pullback G₁ (spMap g))
    have hTX := isGrpPullback_pullback X (spMap fK₂)
    have hXG := isGrpPullback_pullback G₁ (jK V₁)
    have hsq : spMap fK₂ ≫ jK V₁ = jK W ≫ spMap g := by
      show spMap fK₂ ≫ spMap (algebraMap V₁ _) = spMap (algebraMap W _) ≫ spMap g
      rw [GlobalTheory.PolSemiAbModel.spMap_comp', GlobalTheory.PolSemiAbModel.spMap_comp', hK₂]
    have hTG := (hTX.comp hXG).congr hsq rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso gen₁
    have hTP := (hTX.comp (hXY.comp hpb₁)).congr
      (by rw [Category.id_comp, GlobalTheory.PolSemiAbModel.spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, hG.comm, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance, E, hE⟩

end GlobalTheory.SplitSemiAbModel
