import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientKernelPolarisationDescendedBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointEqOfQuotientFamilyIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambdaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiCStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualPol

/- English proof (translation)
Introduce `R _ _ A _ g hA hg L hL ha`. Take `⟨B, P, q, hP, hgood, hfa, hfin, hfl, hsu, hF, hK⟩` from `GlobalTheory.T.exists_quotient_kernel_polarisation_descended_bundle R A g hA hg L hL ha`. Establish `hinj : Inj A P` using `GlobalTheory.T.dualPoint_eq_of_quotient_family_iso R A g hA hg L hL ha B P q hP hfin hfl hsu hF hK`. Establish `hex : ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N → ∃ x : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ x))`. Introduce `T N hN`.

Take `⟨H, h, x, hhf, hhs, hhq, hx⟩` from `GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda R A g hA hg L hL ha T N hN`. Establish `key : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hP.isLB a (y ≫ x ≫ q) = evc hN.isLB a (y ≫ h)`. Introduce `Y a y`. Rewrite using `[hx, ← Category.assoc, hF]`. Establish `hc : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ H.left), g₁ ≫ h.left = g₂ ≫ h.left → g₁ ≫ (x ≫ q).left = g₂ ≫ (x ≫ q).left`.

Introduce `Z g₁ g₂ e`. Set `Z' : Over (Sp R)` to `Over.mk (g₁ ≫ H.hom)`. Establish `e2 : g₂ ≫ H.hom = g₁ ≫ H.hom`. Rewrite using `[← Over.w h, ← Category.assoc, ← e, Category.assoc]`. Set `k₁ : Z' ⟶ H` to `Over.homMk g₁ rfl`.

Set `k₂ : Z' ⟶ H` to `Over.homMk g₂ e2`. Establish `hkh : k₁ ≫ h = k₂ ≫ h` using `Over.OverMorphism.ext e`. Establish `hs : Same A P P (k₁ ≫ x ≫ q) (k₂ ≫ x ≫ q)`. Rewrite using `[same_iff hP.isLB hP.isLB]`. Establish `e₁` using `key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₁)`.

Establish `e₂` using `key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₂)`. Simplify using `only [Category.assoc] at e₁ e₂`. Rewrite using `[e₁, e₂, hkh]`. Use `congrArg (fun t => t.left) (hinj Z' _ _ hs)` as an intermediate fact. Simplify `this` using `[k₁, k₂]`.

Use `haveI : Flat h.left := hhf`. Use `haveI : Surjective h.left := hhs`. Use `haveI : QuasiCompact h.left := hhq`. Set `d : T.left ⟶ B.left` to `EffectiveEpi.desc h.left (x ≫ q).left hc`. Establish `hd : h.left ≫ d = (x ≫ q).left` using `EffectiveEpi.fac h.left (x ≫ q).left hc`.

Establish `hdB : d ≫ B.hom = T.hom`. Rewrite using `[← cancel_epi h.left, ← Category.assoc, hd, Over.w (x ≫ q), Over.w h]`. Set `xT : T ⟶ B` to `Over.homMk d hdB`. Establish `hxT : h ≫ xT = x ≫ q` using `Over.OverMorphism.ext hd`. Use `⟨xT, (same_id_iff hN.isLB hP.isLB xT).1 ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact (Sp R) A hA T B T H N P hN hP (𝟙 T) xT h hhf hhs hhq ?_` and prove the remaining obligations. Rewrite using `[same_iff hN.isLB hP.isLB, Category.comp_id, hxT, key]`. Use `⟨B, toUnit B, P, ⟨hP, fun T t N hN ↦ ?_⟩, hgood, hfa⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hex T N hN`. Use `⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hinj T y x ?_⟩` and prove the remaining obligations.

Establish `h1` using `(cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hy.2`. Establish `h2` using `(cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hx`. Conclude with `(cls_eq_iff (pull_isLB hP.isLB _) (pull_isLB hP.isLB _)).1 (h1.symm.trans h2)`.
-/
theorem hasRepAF_of_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → HasRepAF A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg L hL ha
  obtain ⟨B, P, q, hP, hgood, hfa, hfin, hfl, hsu, hF, hK⟩ := GlobalTheory.T.exists_quotient_kernel_polarisation_descended_bundle R A g hA hg L hL ha
  have hinj : Inj A P := GlobalTheory.T.dualPoint_eq_of_quotient_family_iso R A g hA hg L hL ha B P q hP hfin hfl hsu hF hK
  have hex : ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
      ∃ x : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ x)) := by
    intro T N hN
    obtain ⟨H, h, x, hhf, hhs, hhq, hx⟩ := GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda R A g hA hg L hL ha T N hN
    have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H),
        evc hP.isLB a (y ≫ x ≫ q) = evc hN.isLB a (y ≫ h) := by
      intro Y a y
      rw [hx, ← Category.assoc, hF]
    have hc : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ H.left), g₁ ≫ h.left = g₂ ≫ h.left →
        g₁ ≫ (x ≫ q).left = g₂ ≫ (x ≫ q).left := by
      intro Z g₁ g₂ e
      let Z' : Over (Sp R) := Over.mk (g₁ ≫ H.hom)
      have e2 : g₂ ≫ H.hom = g₁ ≫ H.hom := by
        rw [← Over.w h, ← Category.assoc, ← e, Category.assoc]
      let k₁ : Z' ⟶ H := Over.homMk g₁ rfl
      let k₂ : Z' ⟶ H := Over.homMk g₂ e2
      have hkh : k₁ ≫ h = k₂ ≫ h := Over.OverMorphism.ext e
      have hs : Same A P P (k₁ ≫ x ≫ q) (k₂ ≫ x ≫ q) := by
        rw [same_iff hP.isLB hP.isLB]
        have e₁ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₁)
        have e₂ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₂)
        simp only [Category.assoc] at e₁ e₂
        rw [e₁, e₂, hkh]
      have := congrArg (fun t => t.left) (hinj Z' _ _ hs)
      simpa [k₁, k₂] using this
    haveI : Flat h.left := hhf
    haveI : Surjective h.left := hhs
    haveI : QuasiCompact h.left := hhq
    let d : T.left ⟶ B.left := EffectiveEpi.desc h.left (x ≫ q).left hc
    have hd : h.left ≫ d = (x ≫ q).left := EffectiveEpi.fac h.left (x ≫ q).left hc
    have hdB : d ≫ B.hom = T.hom := by
      rw [← cancel_epi h.left, ← Category.assoc, hd, Over.w (x ≫ q), Over.w h]
    let xT : T ⟶ B := Over.homMk d hdB
    have hxT : h ≫ xT = x ≫ q := Over.OverMorphism.ext hd
    refine ⟨xT, (same_id_iff hN.isLB hP.isLB xT).1 ?_⟩
    refine GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact (Sp R) A hA T B T H N P hN hP (𝟙 T) xT h hhf hhs hhq ?_
    rw [same_iff hN.isLB hP.isLB, Category.comp_id, hxT, key]
  refine ⟨B, toUnit B, P, ⟨hP, fun T t N hN ↦ ?_⟩, hgood, hfa⟩
  obtain ⟨x, hx⟩ := hex T N hN
  refine ⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hinj T y x ?_⟩
  have h1 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hy.2
  have h2 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hx
  exact (cls_eq_iff (pull_isLB hP.isLB _) (pull_isLB hP.isLB _)).1 (h1.symm.trans h2)

end GlobalTheory.DualPol
