import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroAffineMilnorSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ArtinPicGlue

/- English proof (translation)
Break down `subsingleton_or_nontrivial R₀ with h | h` into its components or cases. Conclude with `⟨1, Subsingleton.elim _ _⟩`. Use `haveI := hR h haveI : IsLocalHom g := IsLocalHom.of_surjective g hg`. Take `⟨a, ha⟩` from `hg r`. Conclude with `⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩`.
-/
theorem units_lift_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (hR : Nontrivial R₀ → IsLocalRing R) (g : R →+* R₀)
    (hg : Function.Surjective g) (r : R₀ˣ) : ∃ r' : Rˣ, g r' = r := by
  rcases subsingleton_or_nontrivial R₀ with h | h
  · exact ⟨1, Subsingleton.elim _ _⟩
  · haveI := hR h
    haveI : IsLocalHom g := IsLocalHom.of_surjective g hg
    obtain ⟨a, ha⟩ := hg r
    exact ⟨(isUnit_of_map_unit g a (ha ▸ r.isUnit)).unit, ha⟩

/- English proof (translation)
Establish `hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom` using `IsPullback.of_hasPullback _ _`. Take `⟨G, -, hAb, -⟩` from `GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb`. Use `letI := G`. Establish `hbij` using `GlobalTheory.globalFns_holds _ _ (hAb hA)`. Set `e` to `RingEquiv.ofBijective _ hbij`.

Introduce `u`. Set `u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤)` to `u.1`. Establish `hu' : IsUnit (e.symm u₀)` using `by have := u.isUnit.map e.symm; exact this`. Establish `hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀))` using `hu'.map _`. Take `⟨r₂, hr₂⟩` from `units_lift_of_surjective hR g₂.hom hg₂ hr.unit`.

Establish `hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂))` using `(r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _`. Use `⟨hv.unit, Units.ext ?_⟩` and prove the remaining obligations. Establish `hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) : Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left = (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂`. Rewrite using `[← Over.comp_left, whiskerLeft_snd]`. Both sides reduce to the same expression.

Establish `hn` using `Scheme.ΓSpecIso_inv_naturality g₂`. Establish `h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂)`. Use `congrArg (fun φ => φ.hom (r₂ : R₂)) hn` as an intermediate fact. Conclude with `this.symm`. Establish `key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀`.

Rewrite using `[h1, hr₂, IsUnit.unit_spec]`. Conclude with `congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id`. Establish `h2` using `congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2`. Simplify using `only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]`.

Conclude with `h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))`.
-/
theorem units_lift_baseChange (P R₂ R₀ : CommRingCat.{0}) (f₂ : P ⟶ R₂) (g₂ : R₂ ⟶ R₀) (hR : Nontrivial R₀ → IsLocalRing R₂)
    (hg₂ : Function.Surjective g₂) (A : Over (Spec P)) [GrpObj A] (hA : IsAbelianScheme A) :
    Function.Surjective (Units.map (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left.appTop.hom.toMonoidHom) := by
  have hpb : IsPullback (fst A (Over.mk (Spec.map (f₂ ≫ g₂)))).left (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left
      A.hom (Over.mk (Spec.map (f₂ ≫ g₂))).hom := IsPullback.of_hasPullback _ _
  obtain ⟨G, -, hAb, -⟩ := GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback P R₀ (f₂ ≫ g₂).hom A _ _ _ hpb
  letI := G
  have hbij := GlobalTheory.globalFns_holds _ _ (hAb hA)
  let e := RingEquiv.ofBijective _ hbij
  intro u
  let u₀ : Γ((Over.mk (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left).left, ⊤) := u.1
  have hu' : IsUnit (e.symm u₀) := by have := u.isUnit.map e.symm; exact this
  have hr : IsUnit ((Scheme.ΓSpecIso R₀).hom.hom (e.symm u₀)) := hu'.map _
  obtain ⟨r₂, hr₂⟩ := units_lift_of_surjective hR g₂.hom hg₂ hr.unit
  have hv : IsUnit ((snd A (Over.mk (Spec.map f₂))).left.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) :=
    (r₂.isUnit.map (Scheme.ΓSpecIso R₂).inv.hom).map _
  refine ⟨hv.unit, Units.ext ?_⟩
  have hw : (A ◁ (Over.homMk (Spec.map g₂) (by simp [Spec.map_comp]) :
      Over.mk (Spec.map (f₂ ≫ g₂)) ⟶ Over.mk (Spec.map f₂))).left ≫ (snd A (Over.mk (Spec.map f₂))).left =
      (snd A (Over.mk (Spec.map (f₂ ≫ g₂)))).left ≫ Spec.map g₂ := by
    rw [← Over.comp_left, whiskerLeft_snd]; rfl
  have hn := Scheme.ΓSpecIso_inv_naturality g₂
  have h1 : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) =
      (Scheme.ΓSpecIso R₀).inv.hom (g₂.hom r₂) := by
    have := congrArg (fun φ => φ.hom (r₂ : R₂)) hn
    exact this.symm
  have key : (Spec.map g₂).appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂) = e.symm u₀ := by
    rw [h1, hr₂, IsUnit.unit_spec]
    exact congrArg (fun φ => φ.hom (e.symm u₀)) (Scheme.ΓSpecIso R₀).hom_inv_id
  have h2 := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso R₂).inv.hom r₂)) hw
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2
  simp only [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe]
  exact h2.trans ((congrArg _ key).trans (e.apply_symm_apply u₀))

/- English proof (translation)
Introduce `y`. Take `⟨x, hx⟩` from `hg₁ (g₂ y)`. Establish `H` using `(Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))`. Take `⟨p, -, hp⟩` from `H.2.2 x y hx`. Conclude with `⟨p, hp⟩`.
-/
theorem surjective_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (h : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁) : Function.Surjective f₂ := by
  intro y
  obtain ⟨x, hx⟩ := hg₁ (g₂ y)
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, -, hp⟩ := H.2.2 x y hx
  exact ⟨p, hp⟩

/- English proof (translation)
Introduce `P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂`. Use `haveI : Flat A.hom := by have := hA.smooth; infer_instance`. Establish `hf₂` using `surjective_of_isPullback h hg₁`. Establish `hloc : Nontrivial R₀ → IsLocalRing R₂` using `fun _ => by haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial`. Conclude with `IsLocalRing.of_surjective' f₂.hom hf₂`.

Set `T : Over (Spec P)` to `Over.mk (𝟙 (Spec P))`. Set `T₁ : Over (Spec P)` to `Over.mk (Spec.map f₁)`. Set `T₂ : Over (Spec P)` to `Over.mk (Spec.map f₂)`. Set `T₀ : Over (Spec P)` to `Over.mk (Spec.map (f₂ ≫ g₂))`. Set `j₁ : T₁ ⟶ T` to `Over.homMk (Spec.map f₁) (by simp [T, T₁])`.

Set `j₂ : T₂ ⟶ T` to `Over.homMk (Spec.map f₂) (by simp [T, T₂])`. Set `k₁ : T₀ ⟶ T₁` to `Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])`. Set `k₂ : T₀ ⟶ T₂` to `Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])`. Establish `hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left` using `GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂`. Establish `key` using `GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)`.

Set `s : A ⟶ A ⊗ T` to `lift (𝟙 A) (Over.homMk A.hom (by simp [T]))`. Establish `hs : s.left ≫ (fst A T).left = 𝟙 _` using `by rw [← Over.comp_left, lift_fst]; rfl`. Establish `hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c)`. Rewrite using `[← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]`. Rewrite using `[hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]`.

Rewrite using `[← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]`. Establish `hm` using `h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)`. Rewrite using `[← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]`. Rewrite using `[← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]`. Establish `hm` using `h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)`.

Rewrite using `[← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]`.
-/
theorem pic_eq_zero_of_pull_eq_zero : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h hP _ hg₁ hg₂ A _ A₁ A₂ φ₁ φ₂ hA h₁ h₂ c hc₁ hc₂
  haveI : Flat A.hom := by have := hA.smooth; infer_instance
  have hf₂ := surjective_of_isPullback h hg₁
  have hloc : Nontrivial R₀ → IsLocalRing R₂ := fun _ => by
    haveI : Nontrivial R₂ := g₂.hom.domain_nontrivial
    exact IsLocalRing.of_surjective' f₂.hom hf₂
  let T : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let T₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let T₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let T₀ : Over (Spec P) := Over.mk (Spec.map (f₂ ≫ g₂))
  let j₁ : T₁ ⟶ T := Over.homMk (Spec.map f₁) (by simp [T, T₁])
  let j₂ : T₂ ⟶ T := Over.homMk (Spec.map f₂) (by simp [T, T₂])
  let k₁ : T₀ ⟶ T₁ := Over.homMk (Spec.map g₁) (by simp only [T₀, T₁, Over.mk_hom]; rw [← Spec.map_comp, h.w])
  let k₂ : T₀ ⟶ T₂ := Over.homMk (Spec.map g₂) (by simp [T₀, T₂, Spec.map_comp])
  have hM : GlobalTheory.DualOpen.Milnor j₁.left j₂.left k₁.left k₂.left := GlobalTheory.DualOpen.Milnor.of_isPullback h hg₂
  have key := GlobalTheory.DualOpen.pic_eq_zero_of_milnor (Spec P) A T T₁ T₂ T₀ j₁ j₂ k₁ k₂ hM
    (units_lift_baseChange P R₂ R₀ f₂ g₂ hloc hg₂ A hA)
  let s : A ⟶ A ⊗ T := lift (𝟙 A) (Over.homMk A.hom (by simp [T]))
  have hs : s.left ≫ (fst A T).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst]; rfl
  have hc : c = GlobalTheory.CechPic.pull s.left (GlobalTheory.CechPic.pull (fst A T).left c) := by
    rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id]
  rw [hc, key (GlobalTheory.CechPic.pull (fst A T).left c) ?_ ?_, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₁.lift_fst (fst A T₁).left (snd A T₁).left ((Over.w (fst A T₁)).trans (Over.w (snd A T₁)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₁, map_zero]
  · rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, whiskerLeft_fst]
    have hm := h₂.lift_fst (fst A T₂).left (snd A T₂).left ((Over.w (fst A T₂)).trans (Over.w (snd A T₂)).symm)
    rw [← hm, GlobalTheory.CechPic.pull_comp, hc₂, map_zero]

end GlobalTheory.ArtinPicGlue
