import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open scoped TensorProduct

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `hRL : Function.Injective (algebraMap R (FractionRing A))`. Rewrite using `[IsScalarTower.algebraMap_eq R A (FractionRing A)]`. Conclude with `(IsFractionRing.injective A (FractionRing A)).comp hinj`. Use `haveI : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective R _).mpr hRL`. Use `letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)`.

Use `haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)`. Take `⟨φ, hφ⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing R) (FractionRing A)) (LinearMap.ker_eq_bot.mpr (algebraMap (FractionRing R) (FractionRing A)).injective)`. Establish `hφ1 : φ 1 = 1` using `by simpa using congr($hφ 1)`. Set `Φ : FractionRing A ⊗[R] FractionRing A →ₗ[R] FractionRing A` to `LinearMap.mul' R (FractionRing A) ∘ₗ TensorProduct.map ((Algebra.linearMap (FractionRing R) (FractionRing A) ∘ₗ φ).restrictScalars R) LinearMap.id`. Establish `key` using `congr(Φ $h)`.

Simplify using `only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, LinearMap.id_apply, LinearMap.mul'_apply, hφ1, map_one] at key`. Use `replace key : algebraMap (FractionRing R) (FractionRing A) (φ (algebraMap A (FractionRing A) a)) = algebraMap A (FractionRing A) a := by`. Use `key using 1` and compare the differences between its conclusion and the goal. Conclude with `(_root_.mul_one _).symm`. Conclude with `(_root_.one_mul _).symm`.

Establish `hint : IsIntegral R (φ (algebraMap A (FractionRing A) a))`. Rewrite using `[← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A)) (algebraMap (FractionRing R) (FractionRing A)).injective]`. Express the relevant statement in the definitionally equal form `IsIntegral R (algebraMap (FractionRing R) (FractionRing A) _)`. Rewrite using `[key]`. Conclude with `ha.map (IsScalarTower.toAlgHom R A (FractionRing A))`.

Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Use `⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A), hr, key]`.
-/
theorem mem_range_of_tmul_eq_tmul {R A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A]
    [IsDomain A] [Algebra R A] (hinj : Function.Injective (algebraMap R A)) (a : A) (ha : IsIntegral R a)
    (h : algebraMap A (FractionRing A) a ⊗ₜ[R] (1 : FractionRing A) =
      (1 : FractionRing A) ⊗ₜ[R] algebraMap A (FractionRing A) a) :
    a ∈ Set.range (algebraMap R A) := by
  have hRL : Function.Injective (algebraMap R (FractionRing A)) := by
    rw [IsScalarTower.algebraMap_eq R A (FractionRing A)]
    exact (IsFractionRing.injective A (FractionRing A)).comp hinj
  haveI : FaithfulSMul R (FractionRing A) := (faithfulSMul_iff_algebraMap_injective R _).mpr hRL
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  haveI := FractionRing.isScalarTower_liftAlgebra R (FractionRing A)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing R) (FractionRing A))
    (LinearMap.ker_eq_bot.mpr (algebraMap (FractionRing R) (FractionRing A)).injective)
  have hφ1 : φ 1 = 1 := by simpa using congr($hφ 1)
  let Φ : FractionRing A ⊗[R] FractionRing A →ₗ[R] FractionRing A :=
    LinearMap.mul' R (FractionRing A) ∘ₗ
      TensorProduct.map ((Algebra.linearMap (FractionRing R) (FractionRing A) ∘ₗ φ).restrictScalars R) LinearMap.id
  have key := congr(Φ $h)
  simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, LinearMap.id_apply, LinearMap.mul'_apply, hφ1, map_one] at key
  replace key : algebraMap (FractionRing R) (FractionRing A) (φ (algebraMap A (FractionRing A) a)) =
      algebraMap A (FractionRing A) a := by
    convert key using 1
    · exact (_root_.mul_one _).symm
    · exact (_root_.one_mul _).symm
  have hint : IsIntegral R (φ (algebraMap A (FractionRing A) a)) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A))
      (algebraMap (FractionRing R) (FractionRing A)).injective]
    change IsIntegral R (algebraMap (FractionRing R) (FractionRing A) _)
    rw [key]
    exact ha.map (IsScalarTower.toAlgHom R A (FractionRing A))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A), hr, key]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ S π hP hI hinj x hx`. Take `⟨s⟩ : Nonempty S` from `hI.nonempty`. Take `⟨U, hU, hsU, -⟩` from `exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)`. Use `haveI : Nonempty U := ⟨⟨s, hsU⟩⟩`. Set `res` to `S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op`.

Establish `hres : Function.Injective res.hom` using `map_injective_of_isIntegral S _`. Establish `happ : ∀ t, (π.appLE ⊤ U le_top).hom t = res.hom (π.appTop.hom t)` using `fun t => rfl`. Set `ρ : R →+* Γ(S, U)` to `((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top).hom`. Use `letI : Algebra R Γ(S, U) := ρ.toAlgebra`. Establish `hρ : ∀ t, (π.appLE ⊤ U le_top).hom t = algebraMap R Γ(S, U) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t)`.

Introduce `t`. Express the relevant statement in the definitionally equal form `_ = ρ _`. Simplify using `only [ρ, CommRingCat.hom_comp, RingHom.comp_apply]`. Use `congr 1`. Conclude with `(Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm`.

Establish `hρinj : Function.Injective (algebraMap R Γ(S, U))`. Introduce `a b hab`. Establish `h1 : ∀ c, algebraMap R Γ(S, U) c = res.hom (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))` using `fun c => rfl`. Rewrite `hab` using `[h1, h1]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hinj (hres hab))`.

Use `haveI : UniversallyClosed π := inferInstance`. Establish `hxint : IsIntegral R (res.hom x)`. Take `⟨p, hpm, hp⟩` from `isIntegral_appTop_of_universallyClosed π x`. Use `⟨p.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hpm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Establish `hc : (algebraMap R Γ(S, U)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = res.hom.comp π.appTop.hom`. Use extensionality with `t`. Conclude with `(hρ t).symm.trans (happ t)`. Rewrite using `[hc, ← Polynomial.hom_eval₂, hp, map_zero]`. Establish `H : IsPullback (pullback.fst π π) (pullback.snd π π) π π` using `IsPullback.of_hasPullback π π`.

Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := U) (UX := U) le_top le_top rfl).mp (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _) hU hU)`. Set `j₁ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U)` to `Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))`. Set `j₂ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U)` to `(Algebra.TensorProduct.includeRight : FractionRing Γ(S, U) →ₐ[R] _).toRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))`. Establish `hw : π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₁ : Γ(S, U) ⟶ CommRingCat.of _) = π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₂ : Γ(S, U) ⟶ CommRingCat.of _)`. Use extensionality with `t`.

Express the relevant statement in the definitionally equal form `j₁ ((π.appLE ⊤ U le_top).hom t) = j₂ ((π.appLE ⊤ U le_top).hom t)`. Rewrite using `[hρ]`. Use `show algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _) ⊗ₜ[R] (1 : FractionRing Γ(S, U)) = (1 : FractionRing Γ(S, U)) ⊗ₜ[R] algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _)`. Rewrite using `[← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `hd1` using `congr(($(po.inl_desc _ _ hw)).hom (res.hom x))`.

Establish `hd2` using `congr(($(po.inr_desc _ _ hw)).hom (res.hom x))`. Establish `e1 : ∀ (f : pullback π π ⟶ S) (h : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ f ⁻¹ᵁ U), (f.appLE U _ h).hom (res.hom x) = ((pullback π π).presheaf.map (homOfLE (le_top : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ ⊤)).op).hom (f.appTop.hom x)`. Introduce `f h`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`. Both sides reduce to the same expression.

Establish `hj : j₁ (res.hom x) = j₂ (res.hom x)`. Use `hd1.symm.trans (Eq.trans ?_ hd2)` and prove the remaining obligations. Rewrite using `[CommRingCat.comp_apply, CommRingCat.comp_apply, e1, e1, hx]`. Take `⟨r, hr⟩` from `mem_range_of_tmul_eq_tmul hρinj _ hxint hj`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, hres ?_⟩` and prove the remaining obligations.

Rewrite using `[← happ]`. Conclude with `hr`.
-/
theorem mem_range_appTop_of_fst_eq_snd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤),
    (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  intro R _ _ _ S π hP hI hinj x hx
  obtain ⟨s⟩ : Nonempty S := hI.nonempty
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨s, hsU⟩⟩
  let res := S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  have hres : Function.Injective res.hom := map_injective_of_isIntegral S _
  have happ : ∀ t, (π.appLE ⊤ U le_top).hom t = res.hom (π.appTop.hom t) := fun t => rfl
  let ρ : R →+* Γ(S, U) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top).hom
  letI : Algebra R Γ(S, U) := ρ.toAlgebra
  have hρ : ∀ t, (π.appLE ⊤ U le_top).hom t = algebraMap R Γ(S, U) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom t) := by
    intro t
    change _ = ρ _
    simp only [ρ, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) t).symm
  have hρinj : Function.Injective (algebraMap R Γ(S, U)) := by
    intro a b hab
    have h1 : ∀ c, algebraMap R Γ(S, U) c = res.hom (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
      fun c => rfl
    rw [h1, h1] at hab
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective (hinj (hres hab))
  haveI : UniversallyClosed π := inferInstance
  have hxint : IsIntegral R (res.hom x) := by
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed π x
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap R Γ(S, U)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = res.hom.comp π.appTop.hom := by
      ext t
      exact (hρ t).symm.trans (happ t)
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have H : IsPullback (pullback.fst π π) (pullback.snd π π) π π := IsPullback.of_hasPullback π π
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := U) (UX := U) le_top le_top rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top rfl (isAffineOpen_top _) hU hU)
  let j₁ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  let j₂ : Γ(S, U) →+* FractionRing Γ(S, U) ⊗[R] FractionRing Γ(S, U) :=
    (Algebra.TensorProduct.includeRight : FractionRing Γ(S, U) →ₐ[R] _).toRingHom.comp
      (algebraMap Γ(S, U) (FractionRing Γ(S, U)))
  have hw : π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₁ : Γ(S, U) ⟶ CommRingCat.of _) =
      π.appLE ⊤ U le_top ≫ (CommRingCat.ofHom j₂ : Γ(S, U) ⟶ CommRingCat.of _) := by
    ext t
    change j₁ ((π.appLE ⊤ U le_top).hom t) = j₂ ((π.appLE ⊤ U le_top).hom t)
    rw [hρ]
    show algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _) ⊗ₜ[R] (1 : FractionRing Γ(S, U)) =
      (1 : FractionRing Γ(S, U)) ⊗ₜ[R] algebraMap Γ(S, U) (FractionRing Γ(S, U)) (algebraMap R Γ(S, U) _)
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hd1 := congr(($(po.inl_desc _ _ hw)).hom (res.hom x))
  have hd2 := congr(($(po.inr_desc _ _ hw)).hom (res.hom x))
  have e1 : ∀ (f : pullback π π ⟶ S) (h : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ f ⁻¹ᵁ U),
      (f.appLE U _ h).hom (res.hom x) =
        ((pullback π π).presheaf.map (homOfLE (le_top : pullback.fst π π ⁻¹ᵁ U ⊓ pullback.snd π π ⁻¹ᵁ U ≤ ⊤)).op).hom
          (f.appTop.hom x) := by
    intro f h
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  have hj : j₁ (res.hom x) = j₂ (res.hom x) := by
    refine hd1.symm.trans (Eq.trans ?_ hd2)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, e1, e1, hx]
  obtain ⟨r, hr⟩ := mem_range_of_tmul_eq_tmul hρinj _ hxint hj
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, hres ?_⟩
  rw [← happ]
  exact hr

end GlobalTheory.Mum
