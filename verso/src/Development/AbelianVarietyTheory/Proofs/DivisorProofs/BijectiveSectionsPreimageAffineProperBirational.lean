import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory

open TopologicalSpace

namespace GlobalTheory.ZariskiSections

/- English proof (translation)
Use `⟨fun a a' e => IsFractionRing.injective A K (by rw [← h, ← h, e]), fun b => ?_⟩` and prove the remaining obligations. Use `letI := φ.toAlgebra`. Establish `: Module.Finite A B` using `hφ`. Establish `hb : _root_.IsIntegral A b` using `Algebra.IsIntegral.isIntegral b`. Set `θ' : B →ₐ[A] K` to `{ θ with commutes' := fun a => h a }`.

Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (hb.map θ')`. Conclude with `⟨a, hθ (by rw [h]; exact ha)⟩`.
-/
theorem bijective_of_finite_of_fractionRing {A B K : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : A →+* B) (hφ : φ.Finite) (θ : B →+* K) (hθ : Function.Injective θ)
    (h : ∀ a, θ (φ a) = algebraMap A K a) : Function.Bijective φ := by
  refine ⟨fun a a' e => IsFractionRing.injective A K (by rw [← h, ← h, e]), fun b => ?_⟩
  letI := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : _root_.IsIntegral A b := Algebra.IsIntegral.isIntegral b
  let θ' : B →ₐ[A] K := { θ with commutes' := fun a => h a }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hb.map θ')
  exact ⟨a, hθ (by rw [h]; exact ha)⟩

/- English proof (translation)
Set `f : (π ⁻¹ᵁ V).toScheme ⟶ Spec (.of Γ(Z, V))` to `(π ∣_ V) ≫ hV.isoSpec.hom`. Establish `: IsNoetherianRing Γ(Z, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Use `letI := GlobalTheory.algebraΓOfHom f`. Establish `h1` using `GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule _) 0`. Establish `h2 : Module.Finite Γ(Z, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤)` using `Module.Finite.equiv ((GlobalTheory.coh.zeroUnitEquiv _).restrictScalars Γ(Z, V))`.

Set `e` to `(Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ hV.isoSpec.hom.appTop`. Use `haveI : IsIso hV.isoSpec.hom.appTop := by first`. Consider the case `exact (inferInstance : IsIso (Scheme.Γ.map hV.isoSpec.hom.op))`. Consider the case `exact Scheme.Hom.isIso_app _ ⊤ (by simp)`. Consider the case `exact Scheme.Hom.isIso_app _ ⊤ (fun x _ => (ConcreteCategory.bijective_of_isIso hV.isoSpec.hom.base).2 x)`.

Use `haveI he' : IsIso e := by dsimp only [e]; infer_instance`. Establish `h3 : (e ≫ (π ∣_ V).appTop).hom.Finite`. Establish `he : e ≫ (π ∣_ V).appTop = (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ f.appTop`. Simplify using `only [e, f, Scheme.Hom.comp_appTop, Category.assoc]`. Rewrite using `[he]`.

Conclude with `h2`. Establish `h4 : (π ∣_ V).appTop = inv e ≫ (e ≫ (π ∣_ V).appTop)` using `by rw [IsIso.inv_hom_id_assoc]`. Rewrite using `[h4, CommRingCat.hom_comp]`. Conclude with `RingHom.Finite.comp h3 (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (inv e)).2)`.
-/
theorem finite_appTop_restrict {Y Z : Scheme.{0}} (π : Y ⟶ Z) [IsProper π] [IsLocallyNoetherian Z]
    {V : Z.Opens} (hV : IsAffineOpen V) : (π ∣_ V).appTop.hom.Finite := by
  let f : (π ⁻¹ᵁ V).toScheme ⟶ Spec (.of Γ(Z, V)) := (π ∣_ V) ≫ hV.isoSpec.hom
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := GlobalTheory.algebraΓOfHom f
  have h1 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule _) 0
  have h2 : Module.Finite Γ(Z, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) :=
    Module.Finite.equiv ((GlobalTheory.coh.zeroUnitEquiv _).restrictScalars Γ(Z, V))
  let e := (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ hV.isoSpec.hom.appTop
  haveI : IsIso hV.isoSpec.hom.appTop := by
    first
    | exact (inferInstance : IsIso (Scheme.Γ.map hV.isoSpec.hom.op))
    | exact Scheme.Hom.isIso_app _ ⊤ (by simp)
    | exact Scheme.Hom.isIso_app _ ⊤ (fun x _ => (ConcreteCategory.bijective_of_isIso hV.isoSpec.hom.base).2 x)
  haveI he' : IsIso e := by dsimp only [e]; infer_instance
  have h3 : (e ≫ (π ∣_ V).appTop).hom.Finite := by
    have he : e ≫ (π ∣_ V).appTop = (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ f.appTop := by
      simp only [e, f, Scheme.Hom.comp_appTop, Category.assoc]
    rw [he]
    exact h2
  have h4 : (π ∣_ V).appTop = inv e ≫ (e ≫ (π ∣_ V).appTop) := by rw [IsIso.inv_hom_id_assoc]
  rw [h4, CommRingCat.hom_comp]
  exact RingHom.Finite.comp h3
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (inv e)).2)

/- English proof (translation)
Introduce `Y Z π _ _ _ _ hN U hU hiso V hV`. Establish `hV0 : V.ι ''ᵁ ⊤ = V` using `Scheme.Opens.ι_image_top V`. Establish `hO : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ = π ⁻¹ᵁ V` using `Scheme.Opens.ι_image_top _`. Distinguish the cases in `hne : (V : Set Z).Nonempty`. Use `swap`.

Establish `hVb : V = ⊥`. Use extensionality with `x`. Simplify using `only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Conclude with `fun hx => hne ⟨x, hx⟩`. Establish `s1 : Subsingleton Γ(Z, V.ι ''ᵁ ⊤)` using `CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (hV0.trans hVb))`.

Establish `s2 : Subsingleton Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤)` using `CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty (by`. Rewrite using `[hO]`. Use extensionality with `x`. Simplify using `only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]`. Introduce `hx`.

Conclude with `hne ⟨_, hx⟩))`. Conclude with `⟨fun a b _ => s1.elim a b, fun b => ⟨0, s2.elim _ _⟩⟩`. Use `set η := genericPoint Z`. Establish `hηU : η ∈ U` using `((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)`. Establish `hηV : η ∈ V` using `((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hne)`.

Take `⟨y', hy'⟩` from `(π ∣_ U).surjective ⟨η, hηU⟩`. Use `set y : Y := y'.1`. Establish `hy : π y = η`. Use `congrArg Subtype.val hy'` as an intermediate fact. Simplify `this` using `[morphismRestrict_base_coe]`.

Use `haveI : IsIso (π.stalkMap y) := (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap π U y') |>.mp (inferInstance : IsIso ((π ∣_ U).stalkMap y'))`. Establish `hyO : y ∈ (π ⁻¹ᵁ V).ι ''ᵁ ⊤` using `by rw [hO]; show π y ∈ V; rw [hy]; exact hηV`. Use `haveI : Nonempty (V.ι ''ᵁ ⊤) := ⟨⟨η, hV0.symm ▸ hηV⟩⟩`. Use `haveI := GlobalTheory.IsNormalScheme.of_pred hN`. Establish `hA : IsAffineOpen (V.ι ''ᵁ ⊤)` using `hV0.symm ▸ hV`.

Use `haveI := functionField_isFractionRing_of_isAffineOpen Z _ hA`. Use `haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA`. Set `θ : Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) ⟶ Z.functionField` to `Y.presheaf.germ _ y hyO ≫ inv (π.stalkMap y) ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq hy)).hom`. Establish `hθ : Function.Injective θ.hom`. Simplify using `only [θ, CommRingCat.hom_comp, RingHom.coe_comp]`.

Conclude with `((ConcreteCategory.bijective_of_isIso _).1.comp (ConcreteCategory.bijective_of_isIso _).1).comp (germ_injective_of_isIntegral Y y hyO)`. Use `bijective_of_finite_of_fractionRing (A := Γ(Z, V.ι ''ᵁ ⊤)) (K := Z.functionField) (π ∣_ V).appTop.hom (finite_appTop_restrict π hV) θ.hom hθ fun a => ?_` and prove the remaining obligations. Establish `hle : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (V.ι ''ᵁ ⊤)` using `by rw [hO, hV0]`. Establish `h1 : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op` using `morphismRestrict_app π V ⊤`. Establish `hyV : π y ∈ V.ι ''ᵁ ⊤` using `by rw [hV0, hy]; exact hηV`.

Establish `key : (π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op) ≫ θ = Z.germToFunctionField (V.ι ''ᵁ ⊤)`. Simplify using `only [θ, Category.assoc]`. Rewrite using `[TopCat.Presheaf.germ_res_assoc, ← Scheme.Hom.germ_stalkMap_assoc π (V.ι ''ᵁ ⊤) y hyV, IsIso.hom_inv_id_assoc]`. Conclude with `TopCat.Presheaf.germ_stalkSpecializes _ _ (Inseparable.of_eq hy).specializes'`. Use `congrArg (fun g => g.hom a) key` as an intermediate fact.

Rewrite `this` using `[← h1]`. Conclude with `this`.
-/
theorem bijective_appTop_restrict : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z →
    ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V →
    Function.Bijective (π ∣_ V).appTop := by
  intro Y Z π _ _ _ _ hN U hU hiso V hV
  have hV0 : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hO : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ = π ⁻¹ᵁ V := Scheme.Opens.ι_image_top _
  by_cases hne : (V : Set Z).Nonempty
  swap
  · have hVb : V = ⊥ := by
      ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    have s1 : Subsingleton Γ(Z, V.ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (hV0.trans hVb))
    have s2 : Subsingleton Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty (by
        rw [hO]; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        intro hx; exact hne ⟨_, hx⟩))
    exact ⟨fun a b _ => s1.elim a b, fun b => ⟨0, s2.elim _ _⟩⟩

  set η := genericPoint Z
  have hηU : η ∈ U := ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηV : η ∈ V := ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hne)

  obtain ⟨y', hy'⟩ := (π ∣_ U).surjective ⟨η, hηU⟩
  set y : Y := y'.1
  have hy : π y = η := by
    have := congrArg Subtype.val hy'
    simpa [morphismRestrict_base_coe] using this
  haveI : IsIso (π.stalkMap y) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap π U y') |>.mp
      (inferInstance : IsIso ((π ∣_ U).stalkMap y'))
  have hyO : y ∈ (π ⁻¹ᵁ V).ι ''ᵁ ⊤ := by rw [hO]; show π y ∈ V; rw [hy]; exact hηV
  haveI : Nonempty (V.ι ''ᵁ ⊤) := ⟨⟨η, hV0.symm ▸ hηV⟩⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  have hA : IsAffineOpen (V.ι ''ᵁ ⊤) := hV0.symm ▸ hV
  haveI := functionField_isFractionRing_of_isAffineOpen Z _ hA
  haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA
  let θ : Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) ⟶ Z.functionField :=
    Y.presheaf.germ _ y hyO ≫ inv (π.stalkMap y) ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq hy)).hom
  have hθ : Function.Injective θ.hom := by
    simp only [θ, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso _).1.comp (ConcreteCategory.bijective_of_isIso _).1).comp
      (germ_injective_of_isIntegral Y y hyO)
  refine bijective_of_finite_of_fractionRing (A := Γ(Z, V.ι ''ᵁ ⊤)) (K := Z.functionField)
    (π ∣_ V).appTop.hom (finite_appTop_restrict π hV) θ.hom hθ fun a => ?_
  have hle : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (V.ι ''ᵁ ⊤) := by rw [hO, hV0]
  have h1 : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op :=
    morphismRestrict_app π V ⊤
  have hyV : π y ∈ V.ι ''ᵁ ⊤ := by rw [hV0, hy]; exact hηV
  have key : (π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op) ≫ θ =
      Z.germToFunctionField (V.ι ''ᵁ ⊤) := by
    simp only [θ, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc, ← Scheme.Hom.germ_stalkMap_assoc π (V.ι ''ᵁ ⊤) y hyV,
      IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ (Inseparable.of_eq hy).specializes'
  have := congrArg (fun g => g.hom a) key
  rw [← h1] at this
  exact this

end GlobalTheory.ZariskiSections
