import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj`. Use `haveI := hA`. Use `haveI := hB`. Take `⟨-, haF, haE, -⟩` from `GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ`. Take `⟨-, -, hbE, hbS⟩` from `GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ`.

Use `haveI : IsProper A.hom := IsAbelianScheme.proper`. Use `haveI : IsProper B.hom := IsAbelianScheme.proper`. Use `haveI : Smooth B.hom := IsAbelianScheme.smooth`. Use `haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance`. Use `haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom`.

Use `haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance`. Use `haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom`. Use `haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF`. Use `haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE`. Use `haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE`.

Use `haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS`. Use `haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left`. Use `⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left, Surjective.of_comp ψ'.left ψ.left, ?_⟩` and prove the remaining obligations. Simplify using `[Hecke.PullHecke.transl_one]`. Introduce `a c`.

Simplify using `[Hecke.PullHecke.transl_mul]`. Introduce `a`. Establish `ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ`. Establish `e` using `Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)`. Rewrite `e` using `[Category.id_comp]`.

Rewrite using `[e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]`. Rewrite using `[← Over.comp_left, ht]`. Introduce `K _ _ y y' hyy`. Establish `hz : y' ≫ A.hom = y ≫ A.hom`. Rewrite using `[← Over.w ψ]`.

Simplify using `only [← Category.assoc, hyy]`. Set `Y0 : Over.mk (y ≫ A.hom) ⟶ A` to `Over.homMk y rfl`. Set `Y1 : Over.mk (y ≫ A.hom) ⟶ A` to `Over.homMk y' hz`. Establish `hY : Y1 ≫ ψ = Y0 ≫ ψ`. Use `ext`.

Simplify using `[Y0, Y1, hyy]`. Establish `hg : (Y1 * Y0⁻¹) ≫ ψ = 1`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]`. Take `⟨g₀, hg₀H, hgg₀⟩` from `hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg`. Establish `key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔ toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹)`.

Introduce `h`. Establish `e` using `Hecke.Comp.comp_transl Y0 h`. Prove the components needed by the constructor for the conclusion. Introduce `hh`. Establish `e' : Y0 ≫ Hecke.transl h = Y1`.

Use `ext`. Simplify `hh` using `[Y0, Y1]`. Rewrite `e` using `[e']`. Rewrite using `[e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]`. Introduce `hh`.

Rewrite `e` using `[hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]`. Use `congrArg Over.Hom.left e` as an intermediate fact. Simplify `this` using `[Y0, Y1]`. Use `⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h, hH⟩ hh`.

Establish `h3` using `(key h).mp hh`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]`. Conclude with `mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.galOfKer_holds :
    GalOfKer := by
  intro S A B _ _ _ _ hA hB ψ ψ' κ hψ hψ' h1 h2 hκ H hfin hHψ hinj hsurj
  haveI := hA
  haveI := hB
  obtain ⟨-, haF, haE, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A κ hA hκ
  obtain ⟨-, -, hbE, hbS⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B κ hB hκ
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : IsProper B.hom := IsAbelianScheme.proper
  haveI : Smooth B.hom := IsAbelianScheme.smooth
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : IsSeparated ψ'.left := IsSeparated.of_comp ψ'.left A.hom
  haveI : LocallyOfFiniteType (ψ'.left ≫ A.hom) := by rw [Over.w ψ']; infer_instance
  haveI : LocallyOfFiniteType ψ'.left := locallyOfFiniteType_of_comp ψ'.left A.hom
  haveI : IsFinite (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haF
  haveI : Etale (ψ.left ≫ ψ'.left) := by rw [← Over.comp_left, h1]; exact haE
  haveI : Etale (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbE
  haveI : Surjective (ψ'.left ≫ ψ.left) := by rw [← Over.comp_left, h2]; exact hbS
  haveI : FormallyUnramified ψ'.left := FormallyUnramified.of_comp ψ'.left ψ.left
  refine ⟨hfin, ?_, ?_, ?_, IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left,
    Surjective.of_comp ψ'.left ψ.left, ?_⟩
  · simp [Hecke.PullHecke.transl_one]
  · intro a c
    simp [Hecke.PullHecke.transl_mul]
  · intro a
    have ht : Hecke.transl (a : 𝟙_ (Over S) ⟶ A) ≫ ψ = ψ := by
      have e := Hecke.Comp.comp_transl (𝟙 A) (a : 𝟙_ (Over S) ⟶ A)
      rw [Category.id_comp] at e
      rw [e, MonObj.mul_comp, Category.id_comp, Category.assoc, hHψ a a.2, comp_one, _root_.mul_one]
    rw [← Over.comp_left, ht]
  · intro K _ _ y y' hyy
    have hz : y' ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ]
      simp only [← Category.assoc, hyy]
    let Y0 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    let Y1 : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y' hz
    have hY : Y1 ≫ ψ = Y0 ≫ ψ := by
      ext
      simp [Y0, Y1, hyy]
    have hg : (Y1 * Y0⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hY, _root_.mul_inv_cancel]
    obtain ⟨g₀, hg₀H, hgg₀⟩ := hsurj K (y ≫ A.hom) (Y1 * Y0⁻¹) hg
    have key : ∀ h : 𝟙_ (Over S) ⟶ A, (y ≫ Over.Hom.left (Hecke.transl h) = y' ↔
        toUnit (Over.mk (y ≫ A.hom)) ≫ h = Y1 * Y0⁻¹) := by
      intro h
      have e := Hecke.Comp.comp_transl Y0 h
      constructor
      · intro hh
        have e' : Y0 ≫ Hecke.transl h = Y1 := by
          ext
          simpa [Y0, Y1] using hh
        rw [e'] at e
        rw [e, mul_comm Y0, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
      · intro hh
        rw [hh, mul_comm Y1, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul] at e
        have := congrArg Over.Hom.left e
        simpa [Y0, Y1] using this
    refine ⟨⟨g₀, hg₀H⟩, (key g₀).mpr hgg₀.symm, ?_⟩
    rintro ⟨h, hH⟩ hh
    have h3 := (key h).mp hh
    apply Subtype.ext
    have h4 : toUnit (Over.mk (y ≫ A.hom)) ≫ (h * g₀⁻¹) = 1 := by
      rw [MonObj.comp_mul, GrpObj.comp_inv, h3, hgg₀, _root_.mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj K (y ≫ A.hom) _ (H.mul_mem hH (H.inv_mem hg₀H)) h4)
