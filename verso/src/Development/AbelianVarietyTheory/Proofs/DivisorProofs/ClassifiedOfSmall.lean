import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDualNumberClassifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SmallClassify

/- English proof (translation)
Introduce `R _ X s d hs C _ _ e hee β x₀ hx₀`. Use `haveI : Smooth s := hs.smooth`. Set `πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e})` to `CommRingCat.ofHom (Ideal.Quotient.mk _)`. Establish `hsurj : Function.Surjective πC` using `Ideal.Quotient.mk_surjective`. Use `haveI : IsClosedImmersion (Spec.map πC) := IsClosedImmersion.spec_of_surjective _ hsurj`.

Establish `hnil : IsNilpotent (RingHom.ker πC.hom)`. Use `⟨2, ?_⟩` and prove the remaining obligations. Use `show (RingHom.ker (Ideal.Quotient.mk (Ideal.span {e}))) ^ 2 = ⊥`. Rewrite using `[Ideal.mk_ker, pow_two, Ideal.span_singleton_mul_span_singleton, hee, Ideal.span_singleton_eq_bot.2 rfl]`. Establish `hw : x₀ ≫ s = Spec.map πC ≫ spMap β`.

Rewrite using `[hx₀, GlobalTheory.SiegelRingChange.spMap_comp']`. Take `⟨W, hW, l, hl, hl'⟩` from `GlobalTheory.exists_local_lift_of_smooth s (Spec.map πC) (GlobalTheory.isNilpotent_ker_specMap πC hnil) x₀ (spMap β) hw (IsLocalRing.closedPoint (CommRingCat.of C))`. Establish `hWt : W = ⊤` using `(IsLocalRing.closed_point_mem_iff (R := CommRingCat.of C) (U := W)).mp hW`. Substitute `hWt` using the available equality. Use `haveI : IsIso (⊤ : (Sp C).Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`.

Establish `hU : IsIso ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι` using `isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)`. Use `⟨inv (⊤ : (Sp C).Opens).ι ≫ l, by rw [Category.assoc, hl, IsIso.inv_hom_id_assoc], ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_epi ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι, ← hl', ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← cancel_mono (⊤ : (Sp C).Opens).ι, Category.assoc, IsIso.inv_hom_id, Category.comp_id, morphismRestrict_ι]`.
-/
theorem lift_lemma : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e * e = 0 → ∀ (β : R →+* C) (x₀ : Sp (C ⧸ Ideal.span {e}) ⟶ X), x₀ ≫ s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) → ∃ x₁ : Sp C ⟶ X, x₁ ≫ s = spMap β ∧ spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ x₁ = x₀ := by
  intro R _ X s d hs C _ _ e hee β x₀ hx₀
  haveI : Smooth s := hs.smooth
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hsurj : Function.Surjective πC := Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (Spec.map πC) := IsClosedImmersion.spec_of_surjective _ hsurj
  have hnil : IsNilpotent (RingHom.ker πC.hom) := by
    refine ⟨2, ?_⟩
    show (RingHom.ker (Ideal.Quotient.mk (Ideal.span {e}))) ^ 2 = ⊥
    rw [Ideal.mk_ker, pow_two, Ideal.span_singleton_mul_span_singleton, hee, Ideal.span_singleton_eq_bot.2 rfl]
  have hw : x₀ ≫ s = Spec.map πC ≫ spMap β := by
    rw [hx₀, GlobalTheory.SiegelRingChange.spMap_comp']
  obtain ⟨W, hW, l, hl, hl'⟩ := GlobalTheory.exists_local_lift_of_smooth s (Spec.map πC) (GlobalTheory.isNilpotent_ker_specMap πC hnil)
    x₀ (spMap β) hw (IsLocalRing.closedPoint (CommRingCat.of C))
  have hWt : W = ⊤ := (IsLocalRing.closed_point_mem_iff (R := CommRingCat.of C) (U := W)).mp hW
  subst hWt
  haveI : IsIso (⊤ : (Sp C).Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have hU : IsIso ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  refine ⟨inv (⊤ : (Sp C).Opens).ι ≫ l, by rw [Category.assoc, hl, IsIso.inv_hom_id_assoc], ?_⟩
  rw [← cancel_epi ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι, ← hl', ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (⊤ : (Sp C).Opens).ι, Category.assoc, IsIso.inv_hom_id, Category.comp_id, morphismRestrict_ι]

/- English proof (translation)
Establish `hw : ∀ x, g₁ (f₁ x) = g₂ (f₂ x)` using `fun x => by`. Use `congrArg (fun h : P ⟶ D => h x) w` as an intermediate fact. Simplify using `using this`. Set `Q` to `RingHom.eqLocus (g₁.hom.comp (RingHom.fst A B)) (g₂.hom.comp (RingHom.snd A B))`. Set `φ : P →+* Q` to `(f₁.hom.prod f₂.hom).codRestrict Q (fun x => hw x)`.

Establish `hφ : Function.Bijective φ`. Use `⟨(injective_iff_map_eq_zero φ).2 fun x hx => hinj x ?_ ?_, fun y => ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun z : Q => (z : A × B).1) hx`. Conclude with `congrArg (fun z : Q => (z : A × B).2) hx`. Take `⟨x, h1, h2⟩` from `hsurj (y : A × B).1 (y : A × B).2 y.2`.

Conclude with `⟨x, Subtype.ext (Prod.ext h1 h2)⟩`. Set `E : P ≅ CommRingCat.of Q` to `(RingEquiv.ofBijective φ hφ).toCommRingCatIso`. Establish `h0` using `IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit g₁ g₂)`. Use `IsPullback.of_iso h0 E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)` and prove the remaining obligations. Use extensionality with `y`.

Take `⟨x, rfl⟩` from `hφ.2 y`. Establish `: E.inv (φ x) = x` using `(RingEquiv.ofBijective φ hφ).symm_apply_apply x`. Express the relevant statement in the definitionally equal form `(φ x : A × B).1 = f₁ (E.inv (φ x))`. Rewrite using `[this]`. Both sides reduce to the same expression.

Use extensionality with `y`. Take `⟨x, rfl⟩` from `hφ.2 y`. Establish `: E.inv (φ x) = x` using `(RingEquiv.ofBijective φ hφ).symm_apply_apply x`. Express the relevant statement in the definitionally equal form `(φ x : A × B).2 = f₂ (E.inv (φ x))`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem isPullback_of_bij {P A B D : CommRingCat.{0}} (f₁ : P ⟶ A) (f₂ : P ⟶ B) (g₁ : A ⟶ D) (g₂ : B ⟶ D)
    (w : f₁ ≫ g₁ = f₂ ≫ g₂) (hinj : ∀ x, f₁ x = 0 → f₂ x = 0 → x = 0)
    (hsurj : ∀ a b, g₁ a = g₂ b → ∃ x, f₁ x = a ∧ f₂ x = b) : IsPullback f₁ f₂ g₁ g₂ := by
  have hw : ∀ x, g₁ (f₁ x) = g₂ (f₂ x) := fun x => by
    have := congrArg (fun h : P ⟶ D => h x) w
    simpa using this
  let Q := RingHom.eqLocus (g₁.hom.comp (RingHom.fst A B)) (g₂.hom.comp (RingHom.snd A B))
  let φ : P →+* Q := (f₁.hom.prod f₂.hom).codRestrict Q (fun x => hw x)
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).2 fun x hx => hinj x ?_ ?_, fun y => ?_⟩
    · exact congrArg (fun z : Q => (z : A × B).1) hx
    · exact congrArg (fun z : Q => (z : A × B).2) hx
    · obtain ⟨x, h1, h2⟩ := hsurj (y : A × B).1 (y : A × B).2 y.2
      exact ⟨x, Subtype.ext (Prod.ext h1 h2)⟩
  let E : P ≅ CommRingCat.of Q := (RingEquiv.ofBijective φ hφ).toCommRingCatIso
  have h0 := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit g₁ g₂)
  refine IsPullback.of_iso h0 E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).1 = f₁ (E.inv (φ x))
    rw [this]; rfl
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).2 = f₂ (E.inv (φ x))
    rw [this]; rfl

open IsLocalRing in

/- English proof (translation)
Introduce `C _ _ _ e he hm hne`. Establish `hee : e * e = 0` using `hm e he`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by`. Use `⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Simplify using `using hm a ha`. Both sides reduce to the same expression. Establish `hφ0 : ∀ x, φ x = 0 → x = 0`. Introduce `x hx`. Take `⟨c, rfl⟩` from `residue_surjective x`.

Rewrite `hx` using `[hφ]`. Rewrite using `[residue_eq_zero_iff]`. Assume the negation of the conclusion as `hc`. Establish `hu : IsUnit c` using `by simpa using hc`. Conclude with `hne (hu.mul_right_eq_zero.mp hx)`.

Set `dF : DualNumber (ResidueField C) →+* ResidueField C` to `(TrivSqZeroExt.fstHom (ResidueField C) (ResidueField C) (ResidueField C)).toRingHom`. Set `Ps : Subring (C × DualNumber (ResidueField C))` to `RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) (dF.comp (RingHom.snd _ _))`. Set `p : Ps →+* C` to `(RingHom.fst _ _).comp Ps.subtype`. Set `q : Ps →+* DualNumber (ResidueField C)` to `(RingHom.snd _ _).comp Ps.subtype`. Set `i : C →+* Ps` to `RingHom.codRestrict ((RingHom.id C).prod ((algebraMap (ResidueField C) (DualNumber (ResidueField C))).comp (residue C))) Ps (fun c ↦ rfl)`.

Set `σ : Ps →+* C` to `{ toFun := fun x ↦ x.1.1 + φ x.1.2.snd map_one' := by simp map_zero' := by simp map_add' := by`. Introduce `x y`. Simplify using `only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Use the proof step `map_mul' := by`.

Introduce and unpack `⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩`. Establish `hx' : residue C a = x.fst` using `hx`. Establish `hy' : residue C b = y.fst` using `hy`. Take `⟨c, hc⟩` from `residue_surjective (R := C) x.snd`. Take `⟨d, hd⟩` from `residue_surjective (R := C) y.snd`.

Use `show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)`. Rewrite using `[DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add, hφ, hφ, hφ]`. Take the linear combination `(-(c * d)) * hee }`. Establish `hσi : σ.comp i = RingHom.id C`. Use extensionality with `c`.

Use `show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c`. Simplify using the standard rewrite rules. Establish `hφmem : ∀ x, φ x ∈ Ideal.span {e}`. Introduce `x`. Take `⟨c, rfl⟩` from `residue_surjective x`.

Rewrite using `[hφ]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨c, rfl⟩`. Establish `hunit : ∀ x : Ps, IsUnit (x : C × DualNumber (ResidueField C)).1 → IsUnit x`. Introduce and unpack `⟨⟨a, y⟩, hx⟩ ha`. Establish `hx' : residue C a = y.fst` using `hx`.

Establish `hy : IsUnit y`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hx']`. Conclude with `ha.map _`. Take `⟨u, hu⟩` from `(Prod.isUnit_iff (x := (a, y))).2 ⟨ha, hy⟩`. Establish `hmem : ((u⁻¹ : (C × DualNumber (ResidueField C))ˣ) : C × DualNumber (ResidueField C)) ∈ Ps` using `by show ((residue C).comp (RingHom.fst _ _)) _ = (dF.comp (RingHom.snd _ _)) _`.

Rewrite using `[map_units_inv, map_units_inv, hu]`. Conclude with `congrArg (·⁻¹) hx`. Use `isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (a, y) * _ = 1`. Rewrite using `[← hu, Units.mul_inv]`.

Use `haveI : Nontrivial Ps := nontrivial_of_ne 0 1 (fun h ↦ zero_ne_one (α := C) (congrArg (fun z : Ps ↦ (z : C × DualNumber (ResidueField C)).1) h))`. Establish `hloc : IsLocalRing Ps` using `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ (IsLocalRing.isUnit_or_isUnit_one_sub_self (x : C × DualNumber (ResidueField C)).1).imp (hunit x) (fun h ↦ hunit (1 - x) (by simpa using h))`. Use `letI : Algebra C Ps := i.toAlgebra`. Set `ε' : Ps` to `⟨(0, TrivSqZeroExt.inr 1), by show residue C 0 = (0 : ResidueField C); simp⟩`. Establish `hfin : Module.Finite C Ps` using `by classical`.

Use `⟨⟨({1, ε'} : Finset Ps), eq_top_iff.2 fun x _ ↦ ?_⟩⟩` and prove the remaining obligations. Take `⟨⟨a, y⟩, hx⟩` from `x`. Establish `hx' : residue C a = y.fst` using `hx`. Take `⟨c, hc⟩` from `residue_surjective (R := C) y.snd`. Establish `: (⟨(a, y), hx⟩ : Ps) = a • (1 : Ps) + c • ε'`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, _root_.mul_one]`. Use `Subtype.ext (Prod.ext ?_ ?_)` and prove the remaining obligations. Use `show a = a + c * 0`. Expand and normalize the polynomial expressions, which then agree. Use `show y = TrivSqZeroExt.inl (residue C a) + TrivSqZeroExt.inl (residue C c) * TrivSqZeroExt.inr 1`.

Rewrite using `[TrivSqZeroExt.inl_mul_inr]`. Use `ext`. Rewrite using `[TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hx']`. Rewrite using `[TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_inr, smul_eq_mul, _root_.mul_one, hc]`. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))`. Establish `hart : IsArtinianRing Ps` using `IsArtinianRing.of_finite C Ps`. Use `⟨CommRingCat.of Ps, CommRingCat.ofHom i, CommRingCat.ofHom p, CommRingCat.ofHom σ, CommRingCat.ofHom q, by ext c; rfl, by ext c; exact RingHom.congr_fun hσi c, ?_, ?_, hloc, hart, fun c ↦ ⟨i c, rfl⟩, fun y ↦ ?_⟩` and prove the remaining obligations. Use `isPullback_of_bij _ _ _ _ ?_ ?_ ?_` and prove the remaining obligations. Use extensionality with `x show Ideal.Quotient.mk _ x.1.1 = Ideal.Quotient.mk _ (x.1.1 + φ x.1.2.snd)`.

Use `(Ideal.Quotient.eq.2 ?_).symm` and prove the remaining obligations. Simplify using `using hφmem _`. Introduce and unpack `⟨⟨a, x⟩, hx⟩ h1 h2`. Establish `hx' : residue C a = x.fst` using `hx`. Establish `h1' : a = 0` using `h1`.

Establish `h2' : a + φ x.snd = 0` using `h2`. Substitute `h1'` using the available equality. Rewrite `h2'` using `[zero_add]`. Use `Subtype.ext (Prod.ext rfl ?_)` and prove the remaining obligations. Use `show x = 0`.

Use `ext`. Simplify using `[← hx']`. Simplify using `using hφ0 _ h2'`. Introduce `a b hab`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)`.

Use `⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩` and prove the remaining obligations. Use `show a + φ (residue C c) = b`. Rewrite using `[hφ, hc]`. Expand and normalize the polynomial expressions, which then agree. Use `isPullback_of_bij _ _ _ _ ?_ ?_ ?_` and prove the remaining obligations.

Use extensionality with `x`. Conclude with `x.2`. Introduce `x h1 h2`. Conclude with `Subtype.ext (Prod.ext h1 h2)`. Introduce `a b hab`.

Conclude with `⟨⟨(a, b), hab⟩, rfl, rfl⟩`. Take `⟨a, ha⟩` from `residue_surjective (R := C) y.fst`. Conclude with `⟨⟨(a, y), ha⟩, rfl⟩`.
-/
theorem ring_lemma : ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : CommRingCat.{0}) (i : CommRingCat.of C ⟶ P) (p σ : P ⟶ CommRingCat.of C) (q : P ⟶ CommRingCat.of (DualNumber (IsLocalRing.ResidueField C))), i ≫ p = 𝟙 _ ∧ i ≫ σ = 𝟙 _ ∧ IsPullback p σ (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ∧ IsPullback p q (CommRingCat.ofHom (IsLocalRing.residue C)) (CommRingCat.ofHom (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C)).toRingHom) ∧ IsLocalRing P ∧ IsArtinianRing P ∧ Function.Surjective p ∧ Function.Surjective q := by
  intro C _ _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let dF : DualNumber (ResidueField C) →+* ResidueField C :=
    (TrivSqZeroExt.fstHom (ResidueField C) (ResidueField C) (ResidueField C)).toRingHom
  let Ps : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) (dF.comp (RingHom.snd _ _))
  let p : Ps →+* C := (RingHom.fst _ _).comp Ps.subtype
  let q : Ps →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp Ps.subtype
  let i : C →+* Ps := RingHom.codRestrict ((RingHom.id C).prod
    ((algebraMap (ResidueField C) (DualNumber (ResidueField C))).comp (residue C))) Ps (fun c ↦ rfl)
  let σ : Ps →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add, hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩

  have hunit : ∀ x : Ps, IsUnit (x : C × DualNumber (ResidueField C)).1 → IsUnit x := by
    rintro ⟨⟨a, y⟩, hx⟩ ha
    have hx' : residue C a = y.fst := hx
    have hy : IsUnit y := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hx']
      exact ha.map _
    obtain ⟨u, hu⟩ := (Prod.isUnit_iff (x := (a, y))).2 ⟨ha, hy⟩
    have hmem : ((u⁻¹ : (C × DualNumber (ResidueField C))ˣ) : C × DualNumber (ResidueField C)) ∈ Ps := by
      show ((residue C).comp (RingHom.fst _ _)) _ = (dF.comp (RingHom.snd _ _)) _
      rw [map_units_inv, map_units_inv, hu]
      exact congrArg (·⁻¹) hx
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show (a, y) * _ = 1
    rw [← hu, Units.mul_inv]
  haveI : Nontrivial Ps := nontrivial_of_ne 0 1 (fun h ↦ zero_ne_one (α := C) (congrArg (fun z : Ps ↦ (z : C × DualNumber (ResidueField C)).1) h))
  have hloc : IsLocalRing Ps := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (x : C × DualNumber (ResidueField C)).1).imp (hunit x) (fun h ↦ hunit (1 - x) (by simpa using h))

  letI : Algebra C Ps := i.toAlgebra
  let ε' : Ps := ⟨(0, TrivSqZeroExt.inr 1), by show residue C 0 = (0 : ResidueField C); simp⟩
  have hfin : Module.Finite C Ps := by
    classical
    refine ⟨⟨({1, ε'} : Finset Ps), eq_top_iff.2 fun x _ ↦ ?_⟩⟩
    obtain ⟨⟨a, y⟩, hx⟩ := x
    have hx' : residue C a = y.fst := hx
    obtain ⟨c, hc⟩ := residue_surjective (R := C) y.snd
    have : (⟨(a, y), hx⟩ : Ps) = a • (1 : Ps) + c • ε' := by
      rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one]
      refine Subtype.ext (Prod.ext ?_ ?_)
      · show a = a + c * 0
        ring
      · show y = TrivSqZeroExt.inl (residue C a) + TrivSqZeroExt.inl (residue C c) * TrivSqZeroExt.inr 1
        rw [TrivSqZeroExt.inl_mul_inr]
        ext
        · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hx']
        · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_inr,
            smul_eq_mul, _root_.mul_one, hc]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hart : IsArtinianRing Ps := IsArtinianRing.of_finite C Ps
  refine ⟨CommRingCat.of Ps, CommRingCat.ofHom i, CommRingCat.ofHom p, CommRingCat.ofHom σ, CommRingCat.ofHom q,
    by ext c; rfl, by ext c; exact RingHom.congr_fun hσi c, ?_, ?_, hloc, hart, fun c ↦ ⟨i c, rfl⟩, fun y ↦ ?_⟩
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      show Ideal.Quotient.mk _ x.1.1 = Ideal.Quotient.mk _ (x.1.1 + φ x.1.2.snd)
      refine (Ideal.Quotient.eq.2 ?_).symm
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      exact x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩
  · obtain ⟨a, ha⟩ := residue_surjective (R := C) y.fst
    exact ⟨⟨(a, y), ha⟩, rfl⟩

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

/- English proof (translation)
Establish `hf' : f ≫ s = s' ≫ spMap (RingHom.id B)`. Rewrite using `[hf, show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]`. Establish `H` using `GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n B B ζ ζ (RingHom.id B) S S' s s' f rfl hf'`. Take `⟨c', hc'⟩` from `H.1 c`. Conclude with `⟨c', hc', H.2.1 c c' hc'⟩`.
-/
theorem pull_ex {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre g n ζ s) :
    ∃ c' : SiegPre g n ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have hf' : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf, show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have H := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n B B ζ ζ (RingHom.id B) S S' s s' f rfl hf'
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

/- English proof (translation)
Introduce `g n hg hn hodd F C _ _ _ e he hme β c hc hcl`. Use `set π := Ideal.Quotient.mk (Ideal.span {e}) with hπ`. Take `⟨c₀, hc₀, -⟩` from `pull_ex (s := spMap β) (s' := spMap (π.comp β)) (spMap π) (spMap_comp' β π).symm c`. Take `⟨x₀, hx₀s, hx₀⟩` from `hcl c₀ hc₀`. Distinguish the cases in `he0 : e = 0`.

Establish `hker : ∀ a ∈ Ideal.span {e}, (RingHom.id C) a = 0`. Introduce `a ha`. Rewrite `ha` using `[he0]`. Simplify using `using Ideal.mem_span_singleton.1 ha`. Set `ψ : C ⧸ Ideal.span {e} →+* C` to `Ideal.Quotient.lift _ (RingHom.id C) hker`.

Establish `hψπ : ψ.comp π = RingHom.id C` using `RingHom.ext fun a => by show ψ (π a) = a`. Conclude with `Ideal.Quotient.lift_mk _ _ _`. Use `⟨spMap ψ ≫ x₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hx₀s, ← spMap_comp', ← RingHom.comp_assoc, hψπ, RingHom.id_comp]`. Establish `h1 : SiegPB c c₀ (spMap ψ)` using `pb_cancel hc₀ (by`.

Rewrite using `[← spMap_comp', hψπ, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]`. Conclude with `pb_id c)`. Conclude with `pb_comp hx₀ h1`. Take `⟨x₁, hx₁s, hx₁⟩` from `lift_lemma _ F.X F.s _ F.smooth C e (hme e he) β x₀ hx₀s`. Take `⟨P, i, p, σ, q, hip, hiσ, sq1, sq2, hPl, hPa, hps, hqs⟩` from `ring_lemma C e he hme he0`.

Set `βP : CommRingCat.of (cycAway n) ⟶ P` to `CommRingCat.ofHom β ≫ i`. Establish `hpβ : Spec.map p ≫ Spec.map βP = spMap β`. Rewrite using `[Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hip, Spec.map_id, Category.id_comp]`. Establish `hσβ : Spec.map σ ≫ Spec.map βP = spMap β`. Rewrite using `[Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hiσ, Spec.map_id, Category.id_comp]`.

Set `k` to `IsLocalRing.ResidueField C`. Set `β' : cycAway n →+* DualNumber k` to `(βP ≫ q).hom`. Establish `hqβ : Spec.map q ≫ Spec.map βP = spMap β'`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Set `πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e})` to `CommRingCat.ofHom π`. Take `⟨c₁, hc₁, hc₁p⟩` from `pull_ex (s' := Spec.map p ≫ Spec.map βP) x₁ (by rw [hx₁s, hpβ]) F.univ`. Take `⟨c₂, hc₂, hc₂p⟩` from `pull_ex (s' := Spec.map σ ≫ Spec.map βP) (𝟙 _) (by rw [Category.id_comp, hσβ]) c`. Take `⟨c₀', hc₀', -⟩` from `pull_ex (s' := Spec.map πC ≫ Spec.map p ≫ Spec.map βP) x₀ (by rw [hx₀s, hpβ, spMap_comp']) F.univ`. Establish `h01 : SiegPB c₀' c₁ (spMap π)` using `pb_cancel hc₁ (by rw [hx₁]; exact hc₀')`.

Establish `h0c : SiegPB c₀' c₀ (𝟙 _)` using `pb_cancel hx₀ (by rw [Category.id_comp]; exact hc₀')`. Establish `h0c' : SiegPB c₀' c (spMap π)` using `by simpa using pb_comp hc₀ h0c`. Establish `h02 : SiegPB c₀' c₂ (spMap π)` using `pb_cancel hc₂ (by rw [Category.comp_id]; exact h0c')`. Take `⟨e', he'p, he'1, he'2⟩` from `GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd P (CommRingCat.of C) (CommRingCat.of C) (CommRingCat.of (C ⧸ Ideal.span {e})) p σ πC πC sq1 hPl hPa Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective βP c₁ c₂ (hc₁p F.princ) (hc₂p hc) ⟨c₀', h01 …`. Take `⟨eε, heε, heεp⟩` from `pull_ex (s' := Spec.map q ≫ Spec.map βP) (Spec.map q) rfl e'`.

Take `⟨eε', heε', heε'p⟩` from `pull_ex (s' := spMap β') (𝟙 _) (by rw [Category.id_comp, hqβ]) eε`. Take `⟨v, hvs, hv₀⟩` from `GlobalTheory.T.siegelObject_dualNumber_classified g n hg hn hodd F k β' eε' (heε'p (heεp he'p))`. Establish `hεε : SiegPB eε eε' (𝟙 _)` using `pb_cancel heε' (by rw [Category.id_comp]; exact pb_id eε)`. Establish `hv : SiegPB eε F.univ v` using `by simpa using pb_comp hv₀ hεε`. Set `ρ : CommRingCat.of C ⟶ CommRingCat.of k` to `CommRingCat.ofHom (IsLocalRing.residue C)`.

Set `ε₀ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k` to `CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom`. Establish `hw : Spec.map ρ ≫ Spec.map p = Spec.map ε₀ ≫ Spec.map q`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, sq2.w]`. Take `⟨ck, hck, -⟩` from `pull_ex (s' := Spec.map ρ ≫ Spec.map p ≫ Spec.map βP) (Spec.map ρ) rfl c₁`. Establish `hk1 : SiegPB ck F.univ (Spec.map ρ ≫ x₁)` using `pb_comp hc₁ hck`.

Establish `hk2 : SiegPB ck eε (Spec.map ε₀)` using `pb_cancel heε (by rw [← hw]; exact pb_comp he'1 hck)`. Establish `hk3 : SiegPB ck F.univ (Spec.map ε₀ ≫ v)` using `pb_comp hv hk2`. Establish `hglue : Spec.map ρ ≫ x₁ = Spec.map ε₀ ≫ v`. Use `F.inj k _ _ _ ck ?_ hk1 hk3` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hx₁s, hvs, ← hpβ, ← hqβ, ← Category.assoc, hw, Category.assoc]`.

Establish `hsq` using `GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique P (CommRingCat.of C) (CommRingCat.of (DualNumber k)) (CommRingCat.of k) p q ρ ε₀ sq2 hPl hPa hps hqs inferInstance`. Take `⟨w, ⟨hw1, hw2⟩, -⟩` from `hsq F.X x₁ v hglue`. Establish `hws : w ≫ F.s = Spec.map βP`. Take `⟨w', -, hu⟩` from `hsq (Sp (cycAway n)) (x₁ ≫ F.s) (v ≫ F.s) (by`. Rewrite using `[← Category.assoc, hglue, Category.assoc])`.

Establish `a1` using `hu (w ≫ F.s) ⟨by rw [← Category.assoc, hw1], by rw [← Category.assoc, hw2]⟩`. Establish `a2` using `hu (Spec.map βP) ⟨by rw [hpβ, hx₁s], by rw [hqβ, hvs]⟩`. Rewrite using `[a1, a2]`. Take `⟨e'', he'', he''p⟩` from `pull_ex (s' := Spec.map βP) w hws F.univ`. Establish `hq1 : SiegPB c₁ e'' (Spec.map p)` using `pb_cancel he'' (by rw [hw1]; exact hc₁)`.

Establish `hq2 : SiegPB eε e'' (Spec.map q)` using `pb_cancel he'' (by rw [hw2]; exact hv)`. Establish `hiso : SiegPB e' e'' (𝟙 _)` using `GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n hn hodd P (CommRingCat.of C) (CommRingCat.of (DualNumber k)) (CommRingCat.of k) p q ρ ε₀ sq2 hPl hPa IsLocalRing.residue_surjective (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩) βP e'' e' c₁ eε (he''p F.princ) he'p hq …`. Use `⟨Spec.map σ ≫ w, by rw [Category.assoc, hws, hσβ], ?_⟩` and prove the remaining obligations. Establish `hcc2 : SiegPB c c₂ (𝟙 _)` using `pb_cancel hc₂ (by rw [Category.id_comp]; exact pb_id c)`. Use `pb_comp he'' (pb_comp hiso (pb_comp he'2 hcc2))` as an intermediate fact.

Simplify using `using this`.
-/
theorem classified_of_small : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F C _ _ _ e he hme β c hc hcl
  set π := Ideal.Quotient.mk (Ideal.span {e}) with hπ
  obtain ⟨c₀, hc₀, -⟩ := pull_ex (s := spMap β) (s' := spMap (π.comp β)) (spMap π) (spMap_comp' β π).symm c
  obtain ⟨x₀, hx₀s, hx₀⟩ := hcl c₀ hc₀
  by_cases he0 : e = 0
  · have hker : ∀ a ∈ Ideal.span {e}, (RingHom.id C) a = 0 := by
      intro a ha
      rw [he0] at ha
      simpa using Ideal.mem_span_singleton.1 ha
    let ψ : C ⧸ Ideal.span {e} →+* C := Ideal.Quotient.lift _ (RingHom.id C) hker
    have hψπ : ψ.comp π = RingHom.id C := RingHom.ext fun a => by
      show ψ (π a) = a
      exact Ideal.Quotient.lift_mk _ _ _
    refine ⟨spMap ψ ≫ x₀, ?_, ?_⟩
    · rw [Category.assoc, hx₀s, ← spMap_comp', ← RingHom.comp_assoc, hψπ, RingHom.id_comp]
    · have h1 : SiegPB c c₀ (spMap ψ) := pb_cancel hc₀ (by
        rw [← spMap_comp', hψπ, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]; exact pb_id c)
      exact pb_comp hx₀ h1
  obtain ⟨x₁, hx₁s, hx₁⟩ := lift_lemma _ F.X F.s _ F.smooth C e (hme e he) β x₀ hx₀s
  obtain ⟨P, i, p, σ, q, hip, hiσ, sq1, sq2, hPl, hPa, hps, hqs⟩ := ring_lemma C e he hme he0
  let βP : CommRingCat.of (cycAway n) ⟶ P := CommRingCat.ofHom β ≫ i
  have hpβ : Spec.map p ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hip, Spec.map_id, Category.id_comp]
  have hσβ : Spec.map σ ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hiσ, Spec.map_id, Category.id_comp]
  let k := IsLocalRing.ResidueField C
  let β' : cycAway n →+* DualNumber k := (βP ≫ q).hom
  have hqβ : Spec.map q ≫ Spec.map βP = spMap β' := by
    rw [← Spec.map_comp]; rfl
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom π
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_ex (s' := Spec.map p ≫ Spec.map βP) x₁ (by rw [hx₁s, hpβ]) F.univ
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_ex (s' := Spec.map σ ≫ Spec.map βP) (𝟙 _) (by rw [Category.id_comp, hσβ]) c
  obtain ⟨c₀', hc₀', -⟩ := pull_ex (s' := Spec.map πC ≫ Spec.map p ≫ Spec.map βP) x₀
    (by rw [hx₀s, hpβ, spMap_comp']) F.univ
  have h01 : SiegPB c₀' c₁ (spMap π) := pb_cancel hc₁ (by rw [hx₁]; exact hc₀')
  have h0c : SiegPB c₀' c₀ (𝟙 _) := pb_cancel hx₀ (by rw [Category.id_comp]; exact hc₀')
  have h0c' : SiegPB c₀' c (spMap π) := by simpa using pb_comp hc₀ h0c
  have h02 : SiegPB c₀' c₂ (spMap π) := pb_cancel hc₂ (by rw [Category.comp_id]; exact h0c')
  obtain ⟨e', he'p, he'1, he'2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd P (CommRingCat.of C) (CommRingCat.of C)
    (CommRingCat.of (C ⧸ Ideal.span {e})) p σ πC πC sq1 hPl hPa Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective βP c₁ c₂ (hc₁p F.princ) (hc₂p hc) ⟨c₀', h01, h02⟩
  obtain ⟨eε, heε, heεp⟩ := pull_ex (s' := Spec.map q ≫ Spec.map βP) (Spec.map q) rfl e'
  obtain ⟨eε', heε', heε'p⟩ := pull_ex (s' := spMap β') (𝟙 _) (by rw [Category.id_comp, hqβ]) eε
  obtain ⟨v, hvs, hv₀⟩ := GlobalTheory.T.siegelObject_dualNumber_classified g n hg hn hodd F k β' eε' (heε'p (heεp he'p))
  have hεε : SiegPB eε eε' (𝟙 _) := pb_cancel heε' (by rw [Category.id_comp]; exact pb_id eε)
  have hv : SiegPB eε F.univ v := by simpa using pb_comp hv₀ hεε
  let ρ : CommRingCat.of C ⟶ CommRingCat.of k := CommRingCat.ofHom (IsLocalRing.residue C)
  let ε₀ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hw : Spec.map ρ ≫ Spec.map p = Spec.map ε₀ ≫ Spec.map q := by
    rw [← Spec.map_comp, ← Spec.map_comp, sq2.w]
  obtain ⟨ck, hck, -⟩ := pull_ex (s' := Spec.map ρ ≫ Spec.map p ≫ Spec.map βP) (Spec.map ρ) rfl c₁
  have hk1 : SiegPB ck F.univ (Spec.map ρ ≫ x₁) := pb_comp hc₁ hck
  have hk2 : SiegPB ck eε (Spec.map ε₀) := pb_cancel heε (by rw [← hw]; exact pb_comp he'1 hck)
  have hk3 : SiegPB ck F.univ (Spec.map ε₀ ≫ v) := pb_comp hv hk2
  have hglue : Spec.map ρ ≫ x₁ = Spec.map ε₀ ≫ v := by
    refine F.inj k _ _ _ ck ?_ hk1 hk3
    rw [Category.assoc, Category.assoc, hx₁s, hvs, ← hpβ, ← hqβ, ← Category.assoc, hw, Category.assoc]
  have hsq := GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique P (CommRingCat.of C) (CommRingCat.of (DualNumber k)) (CommRingCat.of k) p q ρ ε₀ sq2
    hPl hPa hps hqs inferInstance
  obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hsq F.X x₁ v hglue
  have hws : w ≫ F.s = Spec.map βP := by
    obtain ⟨w', -, hu⟩ := hsq (Sp (cycAway n)) (x₁ ≫ F.s) (v ≫ F.s) (by
      rw [← Category.assoc, hglue, Category.assoc])
    have a1 := hu (w ≫ F.s) ⟨by rw [← Category.assoc, hw1], by rw [← Category.assoc, hw2]⟩
    have a2 := hu (Spec.map βP) ⟨by rw [hpβ, hx₁s], by rw [hqβ, hvs]⟩
    rw [a1, a2]
  obtain ⟨e'', he'', he''p⟩ := pull_ex (s' := Spec.map βP) w hws F.univ
  have hq1 : SiegPB c₁ e'' (Spec.map p) := pb_cancel he'' (by rw [hw1]; exact hc₁)
  have hq2 : SiegPB eε e'' (Spec.map q) := pb_cancel he'' (by rw [hw2]; exact hv)
  have hiso : SiegPB e' e'' (𝟙 _) := GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n hn hodd P (CommRingCat.of C) (CommRingCat.of (DualNumber k))
    (CommRingCat.of k) p q ρ ε₀ sq2 hPl hPa IsLocalRing.residue_surjective (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)
    βP e'' e' c₁ eε (he''p F.princ) he'p hq1 he'1 hq2 heε
  refine ⟨Spec.map σ ≫ w, by rw [Category.assoc, hws, hσβ], ?_⟩
  have hcc2 : SiegPB c c₂ (𝟙 _) := pb_cancel hc₂ (by rw [Category.id_comp]; exact pb_id c)
  have := pb_comp he'' (pb_comp hiso (pb_comp he'2 hcc2))
  simpa using this

end GlobalTheory.SmallClassify
