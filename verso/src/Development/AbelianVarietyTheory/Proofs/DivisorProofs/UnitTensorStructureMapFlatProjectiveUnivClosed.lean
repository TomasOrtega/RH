import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem topS_hom_ext {Rg : Type} [CommRing Rg] {Y : Over (Sp Rg)} (u v : Y ⟶ topS Rg) : u = v := by
  have hm : Mono (topS Rg).hom := by
    change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w u, Over.w v]

instance isIso_snd_left {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) :
    IsIso (snd (topS Rg) A).left := by
  have : IsIso (snd (topS Rg) A) := by
    refine ⟨⟨lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A), ?_, ?_⟩⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ (topS_hom_ext _ _) ?_
      simp
    · simp
  exact (Over.forget _).map_isIso (snd (topS Rg) A)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem fA_flat_isProjBy_universallyClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  intro Rg _ A _ L hA hL hamp
  have hsq : IsPullback (snd (topS Rg) A).left (fA A) A.hom (𝟙 (Sp Rg)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (snd (topS Rg) A)⟩
  obtain ⟨hproj, hsm, hpr, -⟩ :=
    GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp Rg) A L hA hL hamp Rg (𝟙 _) _ _ (fA A) hsq
  exact ⟨inferInstance, hproj, inferInstance⟩

end GlobalTheory.HomFixUniv
