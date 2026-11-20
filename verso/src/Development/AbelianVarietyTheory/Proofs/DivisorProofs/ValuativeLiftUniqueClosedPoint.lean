import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Side
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry GlobalTheory.ShFam.GalCarry.Corr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry.Corr

/- English proof (translation)
Substitute `hx` using the available equality. Conclude with `⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) q⟩`.
-/
theorem exists_spec_stalk_of_closedPoint (X : Scheme.{0}) (x : X) (W : Type) [CommRing W] [IsLocalRing W]
    (q : Sp W ⟶ X) (hx : q (IsLocalRing.closedPoint W) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ CommRingCat.of W, Spec.map φ ≫ X.fromSpecStalk x = q := by
  subst hx
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of W) q⟩

/- English proof (translation)
Use `set f := algebraMap (X.presheaf.stalk x) X.functionField with hf`. Rewrite using `[Subring.isIntegrallyClosedIn_iff]`. Introduce `s hs`. Use `set A := (LocalSubring.range f).toSubring`. Use `letI : Algebra (X.presheaf.stalk x) A := (f.codRestrict A (fun y => show f y ∈ Set.range f from ⟨y, rfl⟩)).toAlgebra`.

Use `haveI : IsScalarTower (X.presheaf.stalk x) A X.functionField := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.IsIntegral (X.presheaf.stalk x) A := by`. Use `Algebra.IsIntegral.of_surjective (Algebra.ofId (X.presheaf.stalk x) A) ?_` and prove the remaining obligations. Introduce and unpack `⟨_, y, rfl⟩`. Conclude with `⟨y, rfl⟩`.

Establish `hs' : IsIntegral (X.presheaf.stalk x) s` using `isIntegral_trans s hs`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hs'`. Simplify using `only [A, LocalSubring.range_toSubring]`. Conclude with `⟨y, hy⟩`.
-/
theorem isIntegrallyClosedIn_range_stalk (X : Scheme.{0}) [IsIntegral X] (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsIntegrallyClosedIn (LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField)).toSubring
      X.functionField := by
  set f := algebraMap (X.presheaf.stalk x) X.functionField with hf
  rw [Subring.isIntegrallyClosedIn_iff]
  intro s hs
  set A := (LocalSubring.range f).toSubring
  letI : Algebra (X.presheaf.stalk x) A :=
    (f.codRestrict A (fun y => show f y ∈ Set.range f from ⟨y, rfl⟩)).toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk x) A X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk x) A := by
    refine Algebra.IsIntegral.of_surjective (Algebra.ofId (X.presheaf.stalk x) A) ?_
    rintro ⟨_, y, rfl⟩
    exact ⟨y, rfl⟩
  have hs' : IsIntegral (X.presheaf.stalk x) s := isIntegral_trans s hs
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hs'
  simp only [A, LocalSubring.range_toSubring]
  exact ⟨y, hy⟩

/- English proof (translation)
Assume the negation of the conclusion as `hs`. Use `haveI := isIntegrallyClosedIn_range_stalk X x`. Take `⟨V, hle, hsV⟩` from `LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField)) (x := s) (fun h' => hs (by rwa [LocalSubring.range_toSubring] at h'))`. Conclude with `hsV (h V (GlobalTheory.dominatesStalk_iff_range_le.mpr hle))`.
-/
theorem mem_range_of_forall_dominatesStalk (X : Scheme.{0}) [IsIntegral X] (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (s : X.functionField)
    (h : ∀ W : ValuationSubring X.functionField, GlobalTheory.DominatesStalk W x → s ∈ W) :
    s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  by_contra hs
  haveI := isIntegrallyClosedIn_range_stalk X x
  obtain ⟨V, hle, hsV⟩ :=
    LocalSubring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField)) (x := s)
      (fun h' => hs (by rwa [LocalSubring.range_toSubring] at h'))
  exact hsV (h V (GlobalTheory.dominatesStalk_iff_range_le.mpr hle))

/- English proof (translation)
Introduce `F _ Y Y' p' hp' y hcen`. Use `haveI : IsIntegrallyClosed (Y.X.presheaf.stalk y) := (Var.isNormalScheme Y).isIntegrallyClosed_stalk y`. Establish `hv : ValuativeCriterion.Existence Y'.str`. Establish `h' : UniversallyClosed Y'.str` using `inferInstance`. Rewrite `h'` using `[UniversallyClosed.eq_valuativeCriterion]`.

Conclude with `h'.1`. Establish `lift : ∀ W : ValuationSubring Y.Fn, GlobalTheory.DominatesStalk W y → ∃ q : Sp W ⟶ Y'.X, spMap (algebraMap W Y.Fn) ≫ q = p'`. Introduce `W hW`. Take `⟨l, hl, -⟩` from `GlobalTheory.dominatesStalk_iff_exists_hom.mp hW`. Establish `hsq : p' ≫ Y'.str = spMap (algebraMap W Y.Fn) ≫ (l ≫ Y.str)`.

Rewrite using `[hp', ← Category.assoc]`. Use `congr 1`. Conclude with `hl.symm`. Take `⟨⟨q, q1, -⟩⟩` from `(hv ⟨W, Y.Fn, p', l ≫ Y.str, ⟨hsq⟩⟩).exists_lift`. Conclude with `⟨q, q1⟩`.

Take `⟨W₀, hW₀⟩` from `GlobalTheory.exists_dominatesStalk y`. Take `⟨q₀, hq₀⟩` from `lift W₀ hW₀`. Take `⟨y', hy'⟩ : ∃ y', q₀ (IsLocalRing.closedPoint W₀) = y'` from `⟨_, rfl⟩`. Take `⟨φ₀, hφ₀⟩` from `exists_spec_stalk_of_closedPoint Y'.X _ W₀ q₀ hy'`. Set `χ : Y'.X.presheaf.stalk y' →+* Y.Fn` to `(algebraMap W₀ Y.Fn).comp φ₀.hom`.

Establish `hχ : Spec.map (CommRingCat.ofHom χ) ≫ Y'.X.fromSpecStalk y' = p'`. Rewrite using `[← hq₀, ← hφ₀]`. Use `show Spec.map (φ₀ ≫ CommRingCat.ofHom (algebraMap W₀ Y.Fn)) ≫ _ = _`. Rewrite using `[Spec.map_comp, Category.assoc]`. Establish `hmem : ∀ a, χ a ∈ (algebraMap (Y.X.presheaf.stalk y) Y.Fn).range`.

Introduce `a`. Use `mem_range_of_forall_dominatesStalk Y.X y (χ a) (fun W hW => ?_)` and prove the remaining obligations. Take `⟨q, hq⟩` from `lift W hW`. Take `⟨φ, hφ⟩` from `exists_spec_stalk_of_closedPoint Y'.X _ W q ((hcen W W₀ q q₀ hW hW₀ hq hq₀).trans hy')`. Establish `e : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap W Y.Fn)) ≫ Y'.X.fromSpecStalk y' = Spec.map (CommRingCat.ofHom χ) ≫ Y'.X.fromSpecStalk y'`.

Rewrite using `[hχ, Spec.map_comp, Category.assoc, hφ, ← hq]`. Establish `e'` using `Spec.map_injective ((cancel_mono _).mp e)`. Establish `: χ a = algebraMap W Y.Fn (φ.hom a)` using `(congr($(e') a)).symm`. Rewrite using `[this]`. Conclude with `(φ.hom a).2`.

Set `ι` to `algebraMap (Y.X.presheaf.stalk y) Y.Fn`. Establish `hinj : Function.Injective ι` using `IsFractionRing.injective _ _`. Set `e` to `RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)`. Set `ψ : Y'.X.presheaf.stalk y' →+* Y.X.presheaf.stalk y` to `e.symm.toRingHom.comp (χ.codRestrict ι.range hmem)`. Establish `hψ : ι.comp ψ = χ`.

Use extensionality with `a`. Use `show ι (e.symm ⟨χ a, hmem a⟩) = χ a`. Conclude with `congrArg Subtype.val (e.apply_symm_apply ⟨χ a, hmem a⟩)`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y'.X.fromSpecStalk y', ?_⟩` and prove the remaining obligations. Rewrite using `[← hχ, ← hψ, ← Category.assoc]`.

Use `congr 1`. Conclude with `(Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom ι)).symm`.
-/
theorem extends_stalk_of_unique_centre : ∀ (F : Type) [Field F] (Y Y' : Var F) (p' : Sp Y.Fn ⟶ Y'.X), p' ≫ Y'.str = genericPt Y ≫ Y.str →
    ∀ y : Y.X, (∀ (W₁ W₂ : ValuationSubring Y.Fn) (q₁ : Sp W₁ ⟶ Y'.X) (q₂ : Sp W₂ ⟶ Y'.X),
        GlobalTheory.DominatesStalk W₁ y → GlobalTheory.DominatesStalk W₂ y → spMap (algebraMap W₁ Y.Fn) ≫ q₁ = p' →
        spMap (algebraMap W₂ Y.Fn) ≫ q₂ = p' → q₁ (IsLocalRing.closedPoint W₁) = q₂ (IsLocalRing.closedPoint W₂)) →
      ∃ l : Sp (Y.X.presheaf.stalk y) ⟶ Y'.X, spMap (algebraMap (Y.X.presheaf.stalk y) Y.Fn) ≫ l = p' := by
  intro F _ Y Y' p' hp' y hcen
  haveI : IsIntegrallyClosed (Y.X.presheaf.stalk y) := (Var.isNormalScheme Y).isIntegrallyClosed_stalk y
  have hv : ValuativeCriterion.Existence Y'.str := by
    have h' : UniversallyClosed Y'.str := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h'
    exact h'.1
  have lift : ∀ W : ValuationSubring Y.Fn, GlobalTheory.DominatesStalk W y →
      ∃ q : Sp W ⟶ Y'.X, spMap (algebraMap W Y.Fn) ≫ q = p' := by
    intro W hW
    obtain ⟨l, hl, -⟩ := GlobalTheory.dominatesStalk_iff_exists_hom.mp hW
    have hsq : p' ≫ Y'.str = spMap (algebraMap W Y.Fn) ≫ (l ≫ Y.str) := by
      rw [hp', ← Category.assoc]
      congr 1
      exact hl.symm
    obtain ⟨⟨q, q1, -⟩⟩ := (hv ⟨W, Y.Fn, p', l ≫ Y.str, ⟨hsq⟩⟩).exists_lift
    exact ⟨q, q1⟩
  obtain ⟨W₀, hW₀⟩ := GlobalTheory.exists_dominatesStalk y
  obtain ⟨q₀, hq₀⟩ := lift W₀ hW₀
  obtain ⟨y', hy'⟩ : ∃ y', q₀ (IsLocalRing.closedPoint W₀) = y' := ⟨_, rfl⟩
  obtain ⟨φ₀, hφ₀⟩ := exists_spec_stalk_of_closedPoint Y'.X _ W₀ q₀ hy'
  let χ : Y'.X.presheaf.stalk y' →+* Y.Fn := (algebraMap W₀ Y.Fn).comp φ₀.hom
  have hχ : Spec.map (CommRingCat.ofHom χ) ≫ Y'.X.fromSpecStalk y' = p' := by
    rw [← hq₀, ← hφ₀]
    show Spec.map (φ₀ ≫ CommRingCat.ofHom (algebraMap W₀ Y.Fn)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
  have hmem : ∀ a, χ a ∈ (algebraMap (Y.X.presheaf.stalk y) Y.Fn).range := by
    intro a
    refine mem_range_of_forall_dominatesStalk Y.X y (χ a) (fun W hW => ?_)
    obtain ⟨q, hq⟩ := lift W hW
    obtain ⟨φ, hφ⟩ := exists_spec_stalk_of_closedPoint Y'.X _ W q ((hcen W W₀ q q₀ hW hW₀ hq hq₀).trans hy')
    have e : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap W Y.Fn)) ≫ Y'.X.fromSpecStalk y' =
        Spec.map (CommRingCat.ofHom χ) ≫ Y'.X.fromSpecStalk y' := by
      rw [hχ, Spec.map_comp, Category.assoc, hφ, ← hq]
    have e' := Spec.map_injective ((cancel_mono _).mp e)
    have : χ a = algebraMap W Y.Fn (φ.hom a) := (congr($(e') a)).symm
    rw [this]
    exact (φ.hom a).2
  let ι := algebraMap (Y.X.presheaf.stalk y) Y.Fn
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  let e := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)
  let ψ : Y'.X.presheaf.stalk y' →+* Y.X.presheaf.stalk y :=
    e.symm.toRingHom.comp (χ.codRestrict ι.range hmem)
  have hψ : ι.comp ψ = χ := by
    ext a
    show ι (e.symm ⟨χ a, hmem a⟩) = χ a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨χ a, hmem a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y'.X.fromSpecStalk y', ?_⟩
  rw [← hχ, ← hψ, ← Category.assoc]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom ψ) (CommRingCat.ofHom ι)).symm

end GlobalTheory.ShFam.GalCarry.Corr
