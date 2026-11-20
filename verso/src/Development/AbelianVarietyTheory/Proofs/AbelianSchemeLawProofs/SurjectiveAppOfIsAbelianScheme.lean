import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hab : g ≫ q = (p ≫ ε ≫ g) ≫ q`. Simplify using `only [Category.assoc, hg, reassoc_of% he]`. Establish `hcl` using `isClosedImmersion_equalizer_ι_of_isSeparated q hab`. Set `Z : Set X` to `Set.range (equalizer.ι g (p ≫ ε ≫ g))`. Establish `hZ : IsClosed Z` using `(equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range`.

Set `T₀ : Set T` to `(p '' Zᶜ)ᶜ`. Establish `hT₀c : IsClosed T₀` using `(hp _ hZ.isOpen_compl).isClosed_compl`. Establish `hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t)`. Introduce `t ht x hx`. Establish `hxZ : x ∈ Z`.

Assume the negation of the conclusion as `h`. Conclude with `ht ⟨x, h, hx⟩`. Take `⟨z, rfl⟩` from `hxZ`. Rewrite using `[← hx, ← Scheme.Hom.comp_apply, equalizer.condition]`. Simplify using `only [Scheme.Hom.comp_apply]`.

Establish `hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀`. Introduce and unpack `V hV t ht ⟨x, hx, rfl⟩`. Conclude with `hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)`. Establish `hT₀o : IsOpen T₀`. Rewrite using `[isOpen_iff_forall_mem_open]`.

Introduce `t ht`. Take `⟨V, htV, hV⟩` from `hloc t _ (hfib t ht)`. Conclude with `⟨V, hsub V hV, V.2, htV⟩`. Establish `hall : ∀ t : T, t ∈ T₀`. Introduce `t`.

Take `⟨t', y, ht', hy⟩` from `hmeet (π t)`. Take `⟨V, htV, hV⟩` from `hloc t' y hy`. Conclude with `(hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl`. Use `Scheme.hom_ext_of_forall _ _ fun x ↦ ?_` and prove the remaining obligations. Take `⟨V, htV, hV⟩` from `hloc (p x) _ (hfib _ (hall _))`.

Conclude with `⟨p ⁻¹ᵁ V, htV, hV⟩`.
-/
theorem eq_comp_section_of_local_rigidity {X T Y S : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X)
    (g : X ⟶ Y) (π : T ⟶ S) (q : Y ⟶ S) [IsSeparated q] (he : ε ≫ p = 𝟙 T)
    (hg : g ≫ q = p ≫ π) (hp : IsOpenMap p)
    (hloc : ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) →
      ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g)
    (hconn : ∀ s : S, _root_.IsPreconnected (π ⁻¹' {s}))
    (hmeet : ∀ s : S, ∃ (t : T) (y : Y), π t = s ∧ ∀ x : X, p x = t → g x = y) :
    g = p ≫ ε ≫ g := by
  have hab : g ≫ q = (p ≫ ε ≫ g) ≫ q := by
    simp only [Category.assoc, hg, reassoc_of% he]
  have hcl := isClosedImmersion_equalizer_ι_of_isSeparated q hab
  let Z : Set X := Set.range (equalizer.ι g (p ≫ ε ≫ g))
  have hZ : IsClosed Z := (equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range
  let T₀ : Set T := (p '' Zᶜ)ᶜ
  have hT₀c : IsClosed T₀ := (hp _ hZ.isOpen_compl).isClosed_compl
  have hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t) := by
    intro t ht x hx
    have hxZ : x ∈ Z := by
      by_contra h
      exact ht ⟨x, h, hx⟩
    obtain ⟨z, rfl⟩ := hxZ
    rw [← hx, ← Scheme.Hom.comp_apply, equalizer.condition]
    simp only [Scheme.Hom.comp_apply]
  have hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀ := by
    rintro V hV t ht ⟨x, hx, rfl⟩
    exact hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)
  have hT₀o : IsOpen T₀ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t _ (hfib t ht)
    exact ⟨V, hsub V hV, V.2, htV⟩
  have hall : ∀ t : T, t ∈ T₀ := by
    intro t
    obtain ⟨t', y, ht', hy⟩ := hmeet (π t)
    obtain ⟨V, htV, hV⟩ := hloc t' y hy
    exact (hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, htV, hV⟩ := hloc (p x) _ (hfib _ (hall _))
  exact ⟨p ⁻¹ᵁ V, htV, hV⟩

/- English proof (translation)
Establish `h1 : Function.Surjective (pullback.snd A.hom V.ι).appTop.hom` using `(hG _ _ (TLinPf.isAb_pullback V.ι A hA)).2`. Establish `h2 : Function.Surjective (A.hom ∣_ V).appTop.hom`. Establish `e : A.hom ∣_ V = (pullbackRestrictIsoRestrict A.hom V).inv ≫ pullback.snd A.hom V.ι` using `rfl`. Rewrite using `[e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]`. Conclude with `(ConcreteCategory.bijective_of_isIso ((pullbackRestrictIsoRestrict A.hom V).inv.app ⊤)).2.comp h1`.

Rewrite `h2` using `[morphismRestrict_appTop]`. Establish `h3 : Function.Surjective (A.hom.app (V.ι ''ᵁ ⊤)).hom`. Establish `hb : Function.Bijective (A.left.presheaf.map (eqToHom (image_morphismRestrict_preimage A.hom V ⊤)).op).hom`. Rewrite using `[eqToHom_op]`. Conclude with `ConcreteCategory.bijective_of_isIso (A.left.presheaf.map (eqToHom _))`.

Conclude with `(Function.Surjective.of_comp_iff' hb _).1 h2`. Rewrite `h3` using `[V.ι_image_top]`. Then use the resulting hypothesis.
-/
theorem surjective_app_of_isAbelianScheme (hG : GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (V : S.Opens) :
    Function.Surjective (A.hom.app V).hom := by
  have h1 : Function.Surjective (pullback.snd A.hom V.ι).appTop.hom :=
    (hG _ _ (TLinPf.isAb_pullback V.ι A hA)).2
  have h2 : Function.Surjective (A.hom ∣_ V).appTop.hom := by
    have e : A.hom ∣_ V = (pullbackRestrictIsoRestrict A.hom V).inv ≫ pullback.snd A.hom V.ι := rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      ((pullbackRestrictIsoRestrict A.hom V).inv.app ⊤)).2.comp h1
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Surjective (A.hom.app (V.ι ''ᵁ ⊤)).hom := by
    have hb : Function.Bijective (A.left.presheaf.map
        (eqToHom (image_morphismRestrict_preimage A.hom V ⊤)).op).hom := by
      rw [eqToHom_op]
      exact ConcreteCategory.bijective_of_isIso (A.left.presheaf.map (eqToHom _))
    exact (Function.Surjective.of_comp_iff' hb _).1 h2
  rwa [V.ι_image_top] at h3

/- English proof (translation)
Introduce `hG hR S A B _ _ hA hB f hf`. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Use `hB.proper` as an intermediate fact.

Set `g : A ⊗ A ⟶ B` to `(fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)`. Set `ε : A ⟶ A ⊗ A` to `lift 1 (𝟙 A)`. Set `j : A ⟶ A ⊗ A` to `lift (𝟙 A) 1`. Establish `h1 : (1 : A ⟶ A) ≫ f = 1`. Rewrite using `[Hom.one_def, Category.assoc, hf, Hom.one_def]`.

Establish `hε : ε ≫ g = f`. Simplify using `only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1, inv_one, _root_.one_mul, Category.id_comp]`. Establish `hj : j ≫ g = 1`. Simplify using `only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, _root_.mul_one, inv_mul_cancel]`. Establish `hεp : ε.left ≫ (snd A A).left = 𝟙 A.left`.

Rewrite using `[← Over.comp_left, lift_snd, Over.id_left]`. Establish `hsm : Smooth (snd A A).left`. Express the relevant statement in the definitionally equal form `Smooth (pullback.snd A.hom A.hom)`. Use `infer_instance`. Establish `huc : UniversallyClosed (snd A A).left`.

Express the relevant statement in the definitionally equal form `UniversallyClosed (pullback.snd A.hom A.hom)`. Use `infer_instance`. Establish `hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom` using `fun V ↦ surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V`. Establish `hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S` using `Over.w η[A]`. Establish `hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left`.

Establish `hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom` using `.of_hasPullback A.hom A.hom`. Use `IsPullback.of_right ?_ ?_ hr` and prove the remaining obligations. Establish `: j.left ≫ (fst A A).left = 𝟙 A.left`. Rewrite using `[← Over.comp_left, lift_fst, Over.id_left]`. Rewrite using `[this, hη]`.

Conclude with `IsPullback.of_id_fst`. Rewrite using `[← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]`. Both sides reduce to the same expression. Establish `key : g.left = (snd A A).left ≫ ε.left ≫ g.left`. Use `eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_` and prove the remaining obligations.

Introduce `s`. Use `⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hη]`. Both sides reduce to the same expression. Introduce `x hx`.

Take `⟨z, rfl, rfl⟩` from `Scheme.exists_preimage_of_isPullback hpb x s hx`. Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left, Scheme.Hom.comp_apply]`. Both sides reduce to the same expression. Establish `key' : g = snd A A ≫ f`. Rewrite using `[← hε]`.

Conclude with `Over.OverMorphism.ext key`. Establish `hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f)`. Rewrite using `[← key', mul_inv_cancel_left]`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite `hmul` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp]`.

Rewrite using `[hmul]`. Use `congr 1`.
-/
theorem rigidity_of_local_rigidity : GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → RigiditySt := by
  intro hG hR S A B _ _ hA hB f hf
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := hB.proper
  let g : A ⊗ A ⟶ B := (fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)
  let ε : A ⟶ A ⊗ A := lift 1 (𝟙 A)
  let j : A ⟶ A ⊗ A := lift (𝟙 A) 1
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf, Hom.one_def]
  have hε : ε ≫ g = f := by
    simp only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      inv_one, _root_.one_mul, Category.id_comp]
  have hj : j ≫ g = 1 := by
    simp only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
      _root_.mul_one, inv_mul_cancel]
  have hεp : ε.left ≫ (snd A A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd A A).left := by
    change Smooth (pullback.snd A.hom A.hom); infer_instance
  have huc : UniversallyClosed (snd A A).left := by
    change UniversallyClosed (pullback.snd A.hom A.hom); infer_instance
  have hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left := by
    have hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom := .of_hasPullback A.hom A.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst A A).left = 𝟙 A.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hη]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]
      rfl
  have key : g.left = (snd A A).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp
      ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap
      (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_
    intro s
    refine ⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hη]; rfl
    · intro x hx
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left,
        Scheme.Hom.comp_apply]
      rfl
  have key' : g = snd A A ≫ f := by
    rw [← hε]
    exact Over.OverMorphism.ext key
  have hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f) := by
    rw [← key', mul_inv_cancel_left]
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  rw [hmul]
  congr 1

end GlobalTheory
