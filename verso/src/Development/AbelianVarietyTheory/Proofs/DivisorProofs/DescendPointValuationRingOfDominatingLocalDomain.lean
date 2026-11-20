import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `V K W L _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomm hloc X x f hxf`. Set `c : Sp W` to `IsLocalRing.closedPoint W`. Take `⟨U, hU, hcU, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show f c ∈ (⊤ : X.Opens) from trivial)`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hfU : ∀ a : Sp W, f a ∈ U` using `fun a => ((IsLocalRing.specializes_closedPoint (R := W) a).map f.continuous).mem_open U.isOpen hcU`.

Establish `hrf : Set.range f ⊆ Set.range hU'.fromSpec`. Rewrite using `[hU'.range_fromSpec]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hfU a`. Set `pL : Sp L` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)`.

Establish `hrx : Set.range x ⊆ Set.range hU'.fromSpec`. Rewrite using `[hU'.range_fromSpec]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `e` using `congrArg (fun h : Sp L ⟶ X => h pL) hxf`. Simplify using `only [Scheme.Hom.comp_apply] at e`.

Establish `ha : a = (spMap (algebraMap K L)) pL`. Establish `h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥` using `fun c => Ideal.eq_bot_of_prime c.asIdeal`. Conclude with `PrimeSpectrum.ext ((h a).trans (h _).symm)`. Rewrite using `[ha, e]`. Conclude with `hfU _`.

Establish `hf₁` using `IsOpenImmersion.lift_fac hU'.fromSpec f hrf`. Establish `hx₁` using `IsOpenImmersion.lift_fac hU'.fromSpec x hrx`. Rewrite `hf₁` using `[← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec f hrf)]`. Rewrite `hx₁` using `[← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)]`. Use `set β := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec f hrf) with hβ`.

Use `set α := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hα`. Establish `key : α ≫ CommRingCat.ofHom (algebraMap K L) = β ≫ CommRingCat.ofHom (algebraMap W L)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hx₁, hf₁]`. Conclude with `hxf`.

Establish `key' : ∀ r, algebraMap K L (α.hom r) = algebraMap W L (β.hom r)` using `fun r => by`. Establish `e` using `congrArg (fun h => h.hom r) key`. Simplify `e` using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]`. Establish `hmem : ∀ r, α.hom r ∈ (algebraMap V K).range`. Introduce `r`.

Distinguish the cases in `h0 : α.hom r = 0`. Conclude with `⟨0, by rw [h0, map_zero]⟩`. Break down `ValuationRing.isInteger_or_isInteger V (α.hom r) with ⟨v, hv⟩ | ⟨b, hb⟩` into its components or cases. Conclude with `⟨v, hv⟩`. Distinguish the cases in `hb0 : IsUnit b`.

Take `⟨u, rfl⟩` from `hb0`. Use `⟨((u⁻¹ : Vˣ) : V), ?_⟩` and prove the remaining obligations. Rewrite using `[← inv_inv (α.hom r), ← hb]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, Units.inv_mul, map_one]`.

It suffices to derive a contradiction. Apply `hb0` to reduce the goal to its premises. Apply `(isUnit_map_iff (algebraMap V W) b).1` to reduce the goal to its premises. Use `isUnit_iff_exists_inv.2 ⟨β.hom r, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective W L` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one, ← key', ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hb, ← map_mul, inv_mul_cancel₀ h0, map_one]`. Establish `hinj : Function.Injective (algebraMap V K)` using `IsFractionRing.injective V K`. Set `e : V ≃+* (algebraMap V K).range` to `RingEquiv.ofBijective (algebraMap V K).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩`. Set `χ : Γ(X, U) →+* V` to `e.symm.toRingHom.comp (α.hom.codRestrict _ hmem)`. Establish `hχ : (algebraMap V K).comp χ = α.hom`.

Use extensionality with `r`. Express the relevant statement in the definitionally equal form `algebraMap V K (e.symm ⟨α.hom r, hmem r⟩) = α.hom r`. Use `congrArg Subtype.val (e.apply_symm_apply ⟨α.hom r, hmem r⟩)` as an intermediate fact. Conclude with `this`. Use `⟨Spec.map (CommRingCat.ofHom χ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU'.fromSpec, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx₁, ← Category.assoc]`. Use `congr 1`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `r`.

Conclude with `congrArg (fun h => h r) hχ`.
-/
theorem descend_point_to_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  intro V K W L _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomm hloc X x f hxf
  classical

  let c : Sp W := IsLocalRing.closedPoint W
  obtain ⟨U, hU, hcU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show f c ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hfU : ∀ a : Sp W, f a ∈ U := fun a =>
    ((IsLocalRing.specializes_closedPoint (R := W) a).map f.continuous).mem_open U.isOpen hcU
  have hrf : Set.range f ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    exact hfU a
  let pL : Sp L := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have e := congrArg (fun h : Sp L ⟶ X => h pL) hxf
    simp only [Scheme.Hom.comp_apply] at e
    have ha : a = (spMap (algebraMap K L)) pL := by
      have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
      exact PrimeSpectrum.ext ((h a).trans (h _).symm)
    rw [ha, e]
    exact hfU _
  have hf₁ := IsOpenImmersion.lift_fac hU'.fromSpec f hrf
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec f hrf)] at hf₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set β := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec f hrf) with hβ
  set α := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hα
  have key : α ≫ CommRingCat.ofHom (algebraMap K L) = β ≫ CommRingCat.ofHom (algebraMap W L) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hx₁, hf₁]
    exact hxf
  have key' : ∀ r, algebraMap K L (α.hom r) = algebraMap W L (β.hom r) := fun r => by
    have e := congrArg (fun h => h.hom r) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using e

  have hmem : ∀ r, α.hom r ∈ (algebraMap V K).range := by
    intro r
    by_cases h0 : α.hom r = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger V (α.hom r) with ⟨v, hv⟩ | ⟨b, hb⟩
    · exact ⟨v, hv⟩
    · by_cases hb0 : IsUnit b
      · obtain ⟨u, rfl⟩ := hb0
        refine ⟨((u⁻¹ : Vˣ) : V), ?_⟩
        rw [← inv_inv (α.hom r), ← hb]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      · exfalso
        apply hb0
        apply (isUnit_map_iff (algebraMap V W) b).1
        refine isUnit_iff_exists_inv.2 ⟨β.hom r, ?_⟩
        apply IsFractionRing.injective W L
        rw [map_mul, map_one, ← key', ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hb, ← map_mul,
          inv_mul_cancel₀ h0, map_one]
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h),
      (algebraMap V K).rangeRestrict_surjective⟩
  let χ : Γ(X, U) →+* V := e.symm.toRingHom.comp (α.hom.codRestrict _ hmem)
  have hχ : (algebraMap V K).comp χ = α.hom := by
    ext r
    change algebraMap V K (e.symm ⟨α.hom r, hmem r⟩) = α.hom r
    have := congrArg Subtype.val (e.apply_symm_apply ⟨α.hom r, hmem r⟩)
    exact this
  refine ⟨Spec.map (CommRingCat.ofHom χ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun h => h r) hχ

end GlobalTheory
