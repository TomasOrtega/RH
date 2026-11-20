import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupChartCongruence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.le_def]`. Introduce `V`. Rewrite using `[Scheme.IdealSheafData.ideal_mul]`. Conclude with `Ideal.mul_le_inf.trans inf_le_right`.
-/
private theorem mul_le_right {X : Scheme.{u}} (I J : X.IdealSheafData) :
    I * J ≤ J := by
  rw [Scheme.IdealSheafData.le_def]
  intro V
  rw [Scheme.IdealSheafData.ideal_mul]
  exact Ideal.mul_le_inf.trans inf_le_right

/- English proof (translation)
Establish `: Mono U.ι` using `inferInstance`. Conclude with `(cancel_mono U.ι).mp h`.
-/
private theorem eq_of_comp_ι_eq {X : Scheme.{u}} (U : X.Opens) {W : Scheme.{u}}
    {a b : W ⟶ U.toScheme} (h : a ≫ U.ι = b ≫ U.ι) : a = b := by
  have : Mono U.ι := inferInstance
  exact (cancel_mono U.ι).mp h

/- English proof (translation)
Use `(Scheme.Cover.mkOfCovers ι (fun i => (W i).toScheme) (fun i => (W i).ι) ?_ ?_).hom_ext a b ?_` and prove the remaining obligations. Introduce `x`. Take `⟨i, hi⟩` from `hW x`. Establish `hx : x ∈ Set.range ⇑(W i).ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hi`. Take `⟨y, hy⟩` from `hx`. Conclude with `⟨i, y, hy⟩`. Introduce `i infer_instance`. Introduce `i`.

Conclude with `h i`.
-/
private theorem hom_ext_of_comp_ι_eq_of_opens_cover {X Y : Scheme.{u}} {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : ↥X, ∃ i, x ∈ W i) (a b : X ⟶ Y)
    (h : ∀ i, (W i).ι ≫ a = (W i).ι ≫ b) : a = b := by
  refine (Scheme.Cover.mkOfCovers ι (fun i => (W i).toScheme) (fun i => (W i).ι) ?_ ?_).hom_ext
    a b ?_
  · intro x
    obtain ⟨i, hi⟩ := hW x
    have hx : x ∈ Set.range ⇑(W i).ι := by
      rw [Scheme.Opens.range_ι]
      exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  · intro i
    infer_instance
  · intro i
    exact h i

/- English proof (translation)
Assemble the required witnesses or components as `⟨↥Γ(P, U), inferInstance, ⟨hU.isoSpec⟩⟩`.
-/
private theorem exists_isoSpec_of_isAffineOpen {P : Scheme.{u}} {U : P.Opens}
    (hU : IsAffineOpen U) :
    ∃ (R : Type u) (_ : CommRing R), Nonempty (U.toScheme ≅ Spec (CommRingCat.of R)) :=
  ⟨↥Γ(P, U), inferInstance, ⟨hU.isoSpec⟩⟩

/- English proof (translation)
Use `Scheme.IdealSheafData.ext (funext fun V => ?_)` and prove the remaining obligations. Establish `hV : IsAffineOpen (f ''ᵁ (V : U.Opens))` using `V.2.image_of_isOpenImmersion f`. Establish `he : (V : U.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : U.Opens))`. Simplify using `[Scheme.Hom.preimage_image_eq]`. Simplify using `only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]`.

Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨_, hV⟩ V he, Scheme.IdealSheafData.comap_ideal_eq_map_appLE J f ⟨_, hV⟩ V he, Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) f ⟨_, hV⟩ V he]`. Simplify using `only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]`. Rewrite using `[Ideal.map_mul]`.
-/
theorem comap_mul_of_isOpenImmersion {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (I J : X.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  have hV : IsAffineOpen (f ''ᵁ (V : U.Opens)) := V.2.image_of_isOpenImmersion f
  have he : (V : U.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : U.Opens)) := by
    simp [Scheme.Hom.preimage_image_eq]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨_, hV⟩ V he,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J f ⟨_, hV⟩ V he,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) f ⟨_, hV⟩ V he]
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  rw [Ideal.map_mul]

/- English proof (translation)
Use `⟨Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩), ?_⟩` and prove the remaining obligations. Establish `h` using `(Scheme.IdealSheafData.equivOfIsAffine (X := Spec (CommRingCat.of R))).symm_apply_apply I`. Rewrite `h` using `[Scheme.IdealSheafData.equivOfIsAffine_apply, Scheme.IdealSheafData.equivOfIsAffine_symm_apply]`. Rewrite using `[Blowup.specIdealSheaf_eq_ofIdealTop, Ideal.map_map, ← CommRingCat.hom_comp, (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id, CommRingCat.hom_id, Ideal.map_id]`. Conclude with `h`.
-/
theorem exists_specIdealSheaf_eq (R : Type u) [CommRing R]
    (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    ∃ J : Ideal R, Blowup.specIdealSheaf J = I := by
  refine ⟨Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩), ?_⟩
  have h := (Scheme.IdealSheafData.equivOfIsAffine
      (X := Spec (CommRingCat.of R))).symm_apply_apply I
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply,
    Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at h
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Ideal.map_map, ← CommRingCat.hom_comp,
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  exact h

/- English proof (translation)
Take `⟨t, ht⟩ : ∃ t : (𝔟.comap f).subscheme ⟶ 𝔟.subscheme, (𝔟.comap f).subschemeι ≫ f = t ≫ 𝔟.subschemeι` from `⟨(𝔟.comapIso f).hom ≫ Limits.pullback.snd f 𝔟.subschemeι, by`. Rewrite using `[Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem subschemeι_comap_comp_eq_of_subschemeι_comp_eq {X Y P : Scheme.{u}} (f : X ⟶ Y) (u v : Y ⟶ P)
    (𝔟 : Y.IdealSheafData) (hagree : 𝔟.subschemeι ≫ u = 𝔟.subschemeι ≫ v) :
    (𝔟.comap f).subschemeι ≫ f ≫ u = (𝔟.comap f).subschemeι ≫ f ≫ v := by
  obtain ⟨t, ht⟩ : ∃ t : (𝔟.comap f).subscheme ⟶ 𝔟.subscheme,
      (𝔟.comap f).subschemeι ≫ f = t ≫ 𝔟.subschemeι :=
    ⟨(𝔟.comapIso f).hom ≫ Limits.pullback.snd f 𝔟.subschemeι, by
      rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_hom_fst]⟩
  calc (𝔟.comap f).subschemeι ≫ f ≫ u
      = t ≫ 𝔟.subschemeι ≫ u := by rw [← Category.assoc, ht, Category.assoc]
    _ = t ≫ 𝔟.subschemeι ≫ v := by rw [hagree]
    _ = (𝔟.comap f).subschemeι ≫ f ≫ v := by rw [← Category.assoc, ← ht, Category.assoc]

/- English proof (translation)
Establish `hle : 𝔟.comap f ≤ 𝔟₁`. Rewrite using `[← hmul]`. Conclude with `mul_le_right e 𝔟₁`. Take `⟨t, ht⟩ : ∃ t : 𝔟₁.subscheme ⟶ (𝔟.comap f).subscheme, t ≫ (𝔟.comap f).subschemeι = 𝔟₁.subschemeι` from `⟨Scheme.IdealSheafData.inclusion hle, Scheme.IdealSheafData.inclusion_subschemeι hle⟩`. Establish `h3` using `subschemeι_comap_comp_eq_of_subschemeι_comp_eq f u v 𝔟 hagree`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem subschemeι_comp_eq_of_mul_comap {V V₁ P : Scheme.{u}} (f : V₁ ⟶ V) (u v : V ⟶ P)
    (𝔟 : V.IdealSheafData) (hagree : 𝔟.subschemeι ≫ u = 𝔟.subschemeι ≫ v)
    (e 𝔟₁ : V₁.IdealSheafData) (hmul : e * 𝔟₁ = 𝔟.comap f) :
    𝔟₁.subschemeι ≫ f ≫ u = 𝔟₁.subschemeι ≫ f ≫ v := by
  have hle : 𝔟.comap f ≤ 𝔟₁ := by
    rw [← hmul]
    exact mul_le_right e 𝔟₁
  obtain ⟨t, ht⟩ : ∃ t : 𝔟₁.subscheme ⟶ (𝔟.comap f).subscheme,
      t ≫ (𝔟.comap f).subschemeι = 𝔟₁.subschemeι :=
    ⟨Scheme.IdealSheafData.inclusion hle, Scheme.IdealSheafData.inclusion_subschemeι hle⟩
  have h3 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq f u v 𝔟 hagree
  calc 𝔟₁.subschemeι ≫ f ≫ u
      = (t ≫ (𝔟.comap f).subschemeι) ≫ f ≫ u := by rw [ht]
    _ = t ≫ ((𝔟.comap f).subschemeι ≫ f ≫ u) := by rw [Category.assoc]
    _ = t ≫ ((𝔟.comap f).subschemeι ≫ f ≫ v) := by rw [h3]
    _ = (t ≫ (𝔟.comap f).subschemeι) ≫ f ≫ v := by rw [Category.assoc]
    _ = 𝔟₁.subschemeι ≫ f ≫ v := by rw [ht]

/- English proof (translation)
Take `⟨I, rfl⟩` from `exists_specIdealSheaf_eq R J`. Establish `hq : Blowup.IsBlowupAlongIdealSheaf (Blowup.AffineBlowup.toSpec I) (Blowup.specIdealSheaf I)` using `Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec I`. Take `⟨β, hβ⟩` from `hq.exists_lift p hp.1`. Take `⟨α, hα⟩` from `hp.exists_lift (Blowup.AffineBlowup.toSpec I) hq.1`. Establish `hβα : β ≫ α = 𝟙 B`.

Use `hp.hom_ext hp.1 ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hα, hβ]`. Rewrite using `[Category.id_comp]`. Establish `key` using `subschemeι_comp_eq_of_affineBlowup_lifts I ρ ρ' 𝔞 𝔟₁ (h ≫ β) (h' ≫ β) hagree hpull hcart hfac (by rw [Category.assoc, hβ, hh]) (by rw [Category.assoc, hβ, hh'])`. Establish `hfin` using `congrArg (fun m => m ≫ α) key`.

Simplify using `only [Category.assoc, hβα, Category.comp_id] at hfin`. Conclude with `hfin`.
-/
theorem subschemeι_comp_eq_of_blowup_lifts_spec {R : Type u} [CommRing R] {B W : Scheme.{u}}
    (p : B ⟶ Spec (CommRingCat.of R)) (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hp : Blowup.IsBlowupAlongIdealSheaf p J) (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hpull : J.comap ρ = J.comap ρ')
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap ρ))
    (hfac : J.comap ρ * 𝔟₁ = 𝔞)
    (h h' : W ⟶ B) (hh : h ≫ p = ρ) (hh' : h' ≫ p = ρ') :
    𝔟₁.subschemeι ≫ h = 𝔟₁.subschemeι ≫ h' := by
  obtain ⟨I, rfl⟩ := exists_specIdealSheaf_eq R J
  have hq : Blowup.IsBlowupAlongIdealSheaf (Blowup.AffineBlowup.toSpec I) (Blowup.specIdealSheaf I) := Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec I
  obtain ⟨β, hβ⟩ := hq.exists_lift p hp.1
  obtain ⟨α, hα⟩ := hp.exists_lift (Blowup.AffineBlowup.toSpec I) hq.1
  have hβα : β ≫ α = 𝟙 B := by
    refine hp.hom_ext hp.1 ?_ ?_
    · rw [Category.assoc, hα, hβ]
    · rw [Category.id_comp]
  have key := subschemeι_comp_eq_of_affineBlowup_lifts I ρ ρ' 𝔞 𝔟₁ (h ≫ β) (h' ≫ β) hagree hpull hcart hfac
    (by rw [Category.assoc, hβ, hh]) (by rw [Category.assoc, hβ, hh'])
  have hfin := congrArg (fun m => m ≫ α) key
  simp only [Category.assoc, hβα, Category.comp_id] at hfin
  exact hfin

/- English proof (translation)
Take `⟨R, hR, ⟨e⟩⟩` from `exists_isoSpec_of_isAffineOpen hU`. Set `_ : CommRing R` to `hR`. Establish `hres : (ρ ≫ ψ).resLE U O hO ≫ U.ι = O.ι ≫ (ρ ≫ ψ)`. Rewrite using `[Scheme.Hom.resLE_comp_ι]`. Establish `hres' : (ρ ≫ ψ').resLE U O hO' ≫ U.ι = O.ι ≫ (ρ ≫ ψ')`.

Rewrite using `[Scheme.Hom.resLE_comp_ι]`. Establish `hπS : Blowup.IsBlowupAlongIdealSheaf (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv)` using `(hπ.pullback_snd_of_isOpenImmersion U.ι).comp_iso_hom e`. Establish `hcalc : ∀ (χ : V ⟶ P) (hχ : O ≤ (Opens.map (ρ ≫ χ).base).obj U), ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ χ).resLE U O hχ ≫ e.hom) = ((Z.comap χ).comap ρ).comap O.ι`. Introduce `χ hχ`. Simplify using `only [← Scheme.IdealSheafData.comap_comp]`.

Use `congr 1`. Simplify using `[Scheme.Hom.resLE_comp_ι]`. Establish `hcart_W : Blowup.IsLocallyGeneratedByNonZeroDivisor (((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom))`. Rewrite using `[hcalc ψ hO]`. Conclude with `hcart.comap_of_isOpenImmersion O.ι`.

Establish `hpull_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom) = ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ').resLE U O hO' ≫ e.hom)`. Rewrite using `[hcalc ψ hO, hcalc ψ' hO', hZ]`. Establish `hfac_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom) * 𝔟₁.comap O.ι = (𝔟.comap ρ).comap O.ι`. Rewrite using `[hcalc ψ hO, ← comap_mul_of_isOpenImmersion O.ι, hfac]`. Establish `hagree_W : ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ).resLE U O hO ≫ e.hom) = ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ').resLE U O hO' ≫ e.hom)`.

Establish `step1` using `subschemeι_comap_comp_eq_of_subschemeι_comp_eq ρ ψ ψ' 𝔟 hagree`. Establish `step2` using `subschemeι_comap_comp_eq_of_subschemeι_comp_eq O.ι (ρ ≫ ψ) (ρ ≫ ψ') (𝔟.comap ρ) step1`. Establish `step3 : (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ).resLE U O hO) ≫ U.ι = (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ').resLE U O hO') ≫ U.ι`. Rewrite using `[Category.assoc, Category.assoc, hres, hres']`. Conclude with `step2`.

Establish `step4` using `eq_of_comp_ι_eq U step3`. Rewrite using `[← Category.assoc, ← Category.assoc, step4]`. Establish `hcond : (O.ι ≫ ψ₁) ≫ π = (ρ ≫ ψ).resLE U O hO ≫ U.ι`. Rewrite using `[hres, Category.assoc, hψ₁]`. Establish `hcond' : (O.ι ≫ ψ'₁) ≫ π = (ρ ≫ ψ').resLE U O hO' ≫ U.ι`.

Rewrite using `[hres', Category.assoc, hψ'₁]`. Establish `hh : Limits.pullback.lift (O.ι ≫ ψ₁) ((ρ ≫ ψ).resLE U O hO) hcond ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ).resLE U O hO ≫ e.hom`. Rewrite using `[← Category.assoc, Limits.pullback.lift_snd]`. Establish `hh' : Limits.pullback.lift (O.ι ≫ ψ'₁) ((ρ ≫ ψ').resLE U O hO') hcond' ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ').resLE U O hO' ≫ e.hom`. Rewrite using `[← Category.assoc, Limits.pullback.lift_snd]`.

Establish `key` using `subschemeι_comp_eq_of_blowup_lifts_spec (R := R) (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv) hπS ((ρ ≫ ψ).resLE U O hO ≫ e.hom) ((ρ ≫ ψ').resLE U O hO' ≫ e.hom) ((𝔟.comap ρ).comap O.ι) (𝔟₁.comap O.ι) hagree_W hpull_W hcart_W hfac_W (Limits.pullback.lift (O.ι ≫ …`. Establish `hfin` using `congrArg (fun m => m ≫ Limits.pullback.fst π U.ι) key`. Simplify `hfin` using `only [Category.assoc, Limits.pullback.lift_fst]`.
-/
theorem subschemeι_comap_ι_comp_eq_of_blowup_lifts_affine {P P₁ V V₁ : Scheme.{u}} (π : P₁ ⟶ P)
    (Z : P.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (ψ ψ' : V ⟶ P)
    (hZ : Z.comap ψ = Z.comap ψ') (ρ : V₁ ⟶ V)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Z.comap ψ).comap ρ))
    (ψ₁ ψ'₁ : V₁ ⟶ P₁) (hψ₁ : ψ₁ ≫ π = ρ ≫ ψ) (hψ'₁ : ψ'₁ ≫ π = ρ ≫ ψ')
    (𝔟 : V.IdealSheafData) (hagree : 𝔟.subschemeι ≫ ψ = 𝔟.subschemeι ≫ ψ')
    (𝔟₁ : V₁.IdealSheafData) (hfac : (Z.comap ψ).comap ρ * 𝔟₁ = 𝔟.comap ρ)
    (U : P.Opens) (hU : IsAffineOpen U) (O : V₁.Opens)
    (hO : O ≤ (Opens.map (ρ ≫ ψ).base).obj U)
    (hO' : O ≤ (Opens.map (ρ ≫ ψ').base).obj U) :
    (𝔟₁.comap O.ι).subschemeι ≫ O.ι ≫ ψ₁ = (𝔟₁.comap O.ι).subschemeι ≫ O.ι ≫ ψ'₁ := by
  obtain ⟨R, hR, ⟨e⟩⟩ := exists_isoSpec_of_isAffineOpen hU
  let _ : CommRing R := hR
  have hres : (ρ ≫ ψ).resLE U O hO ≫ U.ι = O.ι ≫ (ρ ≫ ψ) := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hres' : (ρ ≫ ψ').resLE U O hO' ≫ U.ι = O.ι ≫ (ρ ≫ ψ') := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hπS : Blowup.IsBlowupAlongIdealSheaf (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv) :=
    (hπ.pullback_snd_of_isOpenImmersion U.ι).comp_iso_hom e
  have hcalc : ∀ (χ : V ⟶ P) (hχ : O ≤ (Opens.map (ρ ≫ χ).base).obj U),
      ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ χ).resLE U O hχ ≫ e.hom)
        = ((Z.comap χ).comap ρ).comap O.ι := by
    intro χ hχ
    simp only [← Scheme.IdealSheafData.comap_comp]
    congr 1
    simp [Scheme.Hom.resLE_comp_ι]
  have hcart_W : Blowup.IsLocallyGeneratedByNonZeroDivisor (((Z.comap U.ι).comap e.inv).comap
      ((ρ ≫ ψ).resLE U O hO ≫ e.hom)) := by
    rw [hcalc ψ hO]
    exact hcart.comap_of_isOpenImmersion O.ι
  have hpull_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      = ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ').resLE U O hO' ≫ e.hom) := by
    rw [hcalc ψ hO, hcalc ψ' hO', hZ]
  have hfac_W : ((Z.comap U.ι).comap e.inv).comap ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      * 𝔟₁.comap O.ι = (𝔟.comap ρ).comap O.ι := by
    rw [hcalc ψ hO, ← comap_mul_of_isOpenImmersion O.ι, hfac]
  have hagree_W : ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ).resLE U O hO ≫ e.hom)
      = ((𝔟.comap ρ).comap O.ι).subschemeι ≫ ((ρ ≫ ψ').resLE U O hO' ≫ e.hom) := by
    have step1 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq ρ ψ ψ' 𝔟 hagree
    have step2 := subschemeι_comap_comp_eq_of_subschemeι_comp_eq O.ι (ρ ≫ ψ) (ρ ≫ ψ') (𝔟.comap ρ) step1
    have step3 : (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ).resLE U O hO) ≫ U.ι
        = (((𝔟.comap ρ).comap O.ι).subschemeι ≫ (ρ ≫ ψ').resLE U O hO') ≫ U.ι := by
      rw [Category.assoc, Category.assoc, hres, hres']
      exact step2
    have step4 := eq_of_comp_ι_eq U step3
    rw [← Category.assoc, ← Category.assoc, step4]
  have hcond : (O.ι ≫ ψ₁) ≫ π = (ρ ≫ ψ).resLE U O hO ≫ U.ι := by
    rw [hres, Category.assoc, hψ₁]
  have hcond' : (O.ι ≫ ψ'₁) ≫ π = (ρ ≫ ψ').resLE U O hO' ≫ U.ι := by
    rw [hres', Category.assoc, hψ'₁]
  have hh : Limits.pullback.lift (O.ι ≫ ψ₁) ((ρ ≫ ψ).resLE U O hO) hcond
      ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ).resLE U O hO ≫ e.hom := by
    rw [← Category.assoc, Limits.pullback.lift_snd]
  have hh' : Limits.pullback.lift (O.ι ≫ ψ'₁) ((ρ ≫ ψ').resLE U O hO') hcond'
      ≫ (Limits.pullback.snd π U.ι ≫ e.hom) = (ρ ≫ ψ').resLE U O hO' ≫ e.hom := by
    rw [← Category.assoc, Limits.pullback.lift_snd]
  have key := subschemeι_comp_eq_of_blowup_lifts_spec (R := R)
    (Limits.pullback.snd π U.ι ≫ e.hom) ((Z.comap U.ι).comap e.inv) hπS
    ((ρ ≫ ψ).resLE U O hO ≫ e.hom) ((ρ ≫ ψ').resLE U O hO' ≫ e.hom)
    ((𝔟.comap ρ).comap O.ι) (𝔟₁.comap O.ι) hagree_W hpull_W hcart_W hfac_W
    (Limits.pullback.lift (O.ι ≫ ψ₁) ((ρ ≫ ψ).resLE U O hO) hcond)
    (Limits.pullback.lift (O.ι ≫ ψ'₁) ((ρ ≫ ψ').resLE U O hO') hcond') hh hh'
  have hfin := congrArg (fun m => m ≫ Limits.pullback.fst π U.ι) key
  simpa only [Category.assoc, Limits.pullback.lift_fst] using hfin

/- English proof (translation)
Take `⟨s, hs⟩ : ∃ s : Limits.pullback O.ι c.subschemeι ⟶ (c.comap O.ι).subscheme, s ≫ (c.comap O.ι).subschemeι = Limits.pullback.fst O.ι c.subschemeι` from `⟨(c.comapIso O.ι).inv, Scheme.IdealSheafData.comapIso_inv_subschemeι c O.ι⟩`. Establish `hres : c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl ≫ O.ι = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι` using `Scheme.Hom.resLE_comp_ι _ _`. Take `⟨k, hk⟩ : ∃ k : (c.subschemeι ⁻¹ᵁ O).toScheme ⟶ Limits.pullback O.ι c.subschemeι, k ≫ Limits.pullback.fst O.ι c.subschemeι = c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl` from `⟨Limits.pullback.lift _ _ hres, Limits.pullback.lift_fst _ _ _⟩`. Use `⟨k ≫ s, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_preimage_subscheme_to_subscheme_comap {T : Scheme.{u}} (c : T.IdealSheafData)
    (O : T.Opens) :
    ∃ k : (c.subschemeι ⁻¹ᵁ O).toScheme ⟶ (c.comap O.ι).subscheme,
      k ≫ (c.comap O.ι).subschemeι ≫ O.ι = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := by
  obtain ⟨s, hs⟩ : ∃ s : Limits.pullback O.ι c.subschemeι ⟶ (c.comap O.ι).subscheme,
      s ≫ (c.comap O.ι).subschemeι = Limits.pullback.fst O.ι c.subschemeι :=
    ⟨(c.comapIso O.ι).inv, Scheme.IdealSheafData.comapIso_inv_subschemeι c O.ι⟩
  have hres : c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl ≫ O.ι
      = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := Scheme.Hom.resLE_comp_ι _ _
  obtain ⟨k, hk⟩ : ∃ k : (c.subschemeι ⁻¹ᵁ O).toScheme ⟶ Limits.pullback O.ι c.subschemeι,
      k ≫ Limits.pullback.fst O.ι c.subschemeι
        = c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl :=
    ⟨Limits.pullback.lift _ _ hres, Limits.pullback.lift_fst _ _ _⟩
  refine ⟨k ≫ s, ?_⟩
  calc (k ≫ s) ≫ (c.comap O.ι).subschemeι ≫ O.ι
      = k ≫ (s ≫ (c.comap O.ι).subschemeι) ≫ O.ι := by simp only [Category.assoc]
    _ = k ≫ Limits.pullback.fst O.ι c.subschemeι ≫ O.ι := by rw [hs]
    _ = (k ≫ Limits.pullback.fst O.ι c.subschemeι) ≫ O.ι := by rw [Category.assoc]
    _ = c.subschemeι.resLE O (c.subschemeι ⁻¹ᵁ O) le_rfl ≫ O.ι := by rw [hk]
    _ = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι := hres

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_preimage_subscheme_to_subscheme_comap c O`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, Category.assoc]`. Use `_ = k ≫ ((c.comap O.ι).subschemeι ≫ O.ι ≫ g') := by rw [hEqComap]`. Use `_ = (k ≫ (c.comap O.ι).subschemeι ≫ O.ι) ≫ g' := by`.

Rewrite using `[Category.assoc, Category.assoc]`. Use `_ = ((c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι) ≫ g' := by rw [hk]`. Use `_ = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by rw [Category.assoc]`.
-/
private theorem preimage_ι_subschemeι_comp_eq_of_comap_ι {T Y : Scheme.{u}} (c : T.IdealSheafData) (O : T.Opens)
    (f' g' : T ⟶ Y)
    (hEqComap : (c.comap O.ι).subschemeι ≫ O.ι ≫ f' = (c.comap O.ι).subschemeι ≫ O.ι ≫ g') :
    (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
      = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by
  obtain ⟨k, hk⟩ := exists_preimage_subscheme_to_subscheme_comap c O
  calc (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
      = ((c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι) ≫ f' := by rw [Category.assoc]
    _ = (k ≫ (c.comap O.ι).subschemeι ≫ O.ι) ≫ f' := by rw [hk]
    _ = k ≫ ((c.comap O.ι).subschemeι ≫ O.ι ≫ f') := by
        rw [Category.assoc, Category.assoc]
    _ = k ≫ ((c.comap O.ι).subschemeι ≫ O.ι ≫ g') := by rw [hEqComap]
    _ = (k ≫ (c.comap O.ι).subschemeι ≫ O.ι) ≫ g' := by
        rw [Category.assoc, Category.assoc]
    _ = ((c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι) ≫ g' := by rw [hk]
    _ = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by rw [Category.assoc]

/- English proof (translation)
Introduce `X Y S T π Z hπ f g hfg ρ hρ f' g' hf' hg' a hagree c hc`. Establish `hEqOnSubscheme : c.subschemeι ≫ ρ ≫ f = c.subschemeι ≫ ρ ≫ g` using `subschemeι_comp_eq_of_mul_comap ρ f g a hagree ((Z.comap f).comap ρ) c hc`. Establish `main : ∀ x : ↥(c.subscheme), ∃ O : T.Opens, c.subschemeι.base x ∈ O ∧ (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f' = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g'`. Introduce `x`. Establish `hpt : (ρ ≫ f).base (c.subschemeι.base x) = (ρ ≫ g).base (c.subschemeι.base x)`.

Establish `h` using `congrArg (fun m : c.subscheme ⟶ X => m.base x) hEqOnSubscheme`. Simplify using `using h`. Take `⟨U, hxU, hU⟩` from `X.exists_isAffineOpen_mem ((ρ ≫ f).base (c.subschemeι.base x))`. Use `⟨(Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U, ⟨hxU, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (ρ ≫ g).base (c.subschemeι.base x) ∈ U`.

Rewrite using `[← hpt]`. Conclude with `hxU`. Use `preimage_ι_subschemeι_comp_eq_of_comap_ι c _ f' g' ?_` and prove the remaining obligations. Conclude with `subschemeι_comap_ι_comp_eq_of_blowup_lifts_affine π Z hπ f g hfg ρ hρ.1 f' g' hf' hg' a hagree c hc U hU ((Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U) inf_le_left inf_le_right`. Use `choose Ox hOx hOeq using main`.

Use `hom_ext_of_comp_ι_eq_of_opens_cover (fun x : ↥(c.subscheme) => c.subschemeι ⁻¹ᵁ (Ox x)) ?_ _ _ hOeq` and prove the remaining obligations. Introduce `y`. Conclude with `⟨y, hOx y⟩`.
-/
theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := by
  intro X Y S T π Z hπ f g hfg ρ hρ f' g' hf' hg' a hagree c hc
  have hEqOnSubscheme : c.subschemeι ≫ ρ ≫ f = c.subschemeι ≫ ρ ≫ g :=
    subschemeι_comp_eq_of_mul_comap ρ f g a hagree ((Z.comap f).comap ρ) c hc
  have main : ∀ x : ↥(c.subscheme), ∃ O : T.Opens, c.subschemeι.base x ∈ O ∧
      (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ f'
        = (c.subschemeι ⁻¹ᵁ O).ι ≫ c.subschemeι ≫ g' := by
    intro x
    have hpt : (ρ ≫ f).base (c.subschemeι.base x)
        = (ρ ≫ g).base (c.subschemeι.base x) := by
      have h := congrArg (fun m : c.subscheme ⟶ X => m.base x) hEqOnSubscheme
      simpa using h
    obtain ⟨U, hxU, hU⟩ := X.exists_isAffineOpen_mem ((ρ ≫ f).base (c.subschemeι.base x))
    refine ⟨(Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U, ⟨hxU, ?_⟩, ?_⟩
    · show (ρ ≫ g).base (c.subschemeι.base x) ∈ U
      rw [← hpt]
      exact hxU
    · refine preimage_ι_subschemeι_comp_eq_of_comap_ι c _ f' g' ?_
      exact subschemeι_comap_ι_comp_eq_of_blowup_lifts_affine π Z hπ f g hfg ρ hρ.1 f' g' hf' hg' a hagree
        c hc U hU ((Opens.map (ρ ≫ f).base).obj U ⊓ (Opens.map (ρ ≫ g).base).obj U)
        inf_le_left inf_le_right
  choose Ox hOx hOeq using main
  refine hom_ext_of_comp_ι_eq_of_opens_cover (fun x : ↥(c.subscheme) => c.subschemeι ⁻¹ᵁ (Ox x)) ?_ _ _ hOeq
  intro y
  exact ⟨y, hOx y⟩

end FunctorialResolution.EmbeddedResolution

end
