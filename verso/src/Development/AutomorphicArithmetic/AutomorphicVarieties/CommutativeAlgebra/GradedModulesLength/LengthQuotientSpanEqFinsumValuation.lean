import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthDet
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DedekindDomain.Instances

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O D`. Set `f : D →ₗ[O] D` to `Algebra.lmul O D a`. Set `Φ` to `LinearMap.toMatrix b b f`. Establish `hdet : Algebra.norm O a = Φ.det`. Rewrite using `[Algebra.norm_apply, LinearMap.det_toMatrix]`.

Establish `hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `b.equivFun.surjective y`. Simplify using `only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]`. Simplify using `only [Module.Basis.equivFun_apply]`.

Conclude with `LinearMap.toMatrix_mulVec_repr b b f x`. Establish `hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f`. Use extensionality with `x`. Simplify using `only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f, Algebra.coe_lmul_eq_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, mul_comm _ _⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, mul_comm _ _⟩`. Establish `hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin`.

Rewrite using `[hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]`. Set `e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ` to `(Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))`. Rewrite using `[e.length_eq, hdet]`. Conclude with `KStar.Selmer.length_cokernel_eq_addVal_det Φ`.
-/
private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

/- English proof (translation)
Establish `: Algebra.IsIntegral O D` using `Algebra.IsIntegral.of_finite O D`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥`. Use extensionality with `c`.

Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]`. Conclude with `⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h, fun h => by simp [h]⟩`. Establish `hmem : x ∈ RingHom.ker σ` using `hx`. Rewrite `hmem` using `[Ideal.eq_bot_of_comap_eq_bot hker]`. Conclude with `hmem`.
-/
private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
/- English proof (translation)
Establish `: IsScalarTower O (FractionRing O) K` using `FractionRing.isScalarTower_liftAlgebra O K`. Set `M` to `Algebra.algebraMapSubmonoid D O⁰`. Set `L` to `Localization M`. Establish `hM : M ≤ D⁰`. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Conclude with `mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))`. Establish `: IsDomain L` using `IsLocalization.isDomain_localization hM`. Establish `hF : IsField L`. Establish `: Module.Finite (FractionRing O) L` using `Module.Finite.of_isLocalization O D O⁰`. Conclude with `isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))`.

Use `letI : Field L := hF.toField`. Use `letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D`. Establish `: Module.Finite (FractionRing O) L` using `Module.Finite.of_isLocalization O D O⁰`. Establish `hN : Algebra.norm (FractionRing O) (algebraMap D L a) = algebraMap O (FractionRing O) (Algebra.norm O a)` using `Algebra.norm_localization O O⁰ a`. Establish `hE` using `Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)`.

Set `r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K)` to `fun τ => (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)`. Establish `hinj : Function.Injective r`. Introduce `τ₁ τ₂ h`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext M` to reduce the goal to its premises.

Use extensionality with `d`. Conclude with `DFunLike.congr_fun h d`. Establish `hsurj : Function.Surjective r`. Introduce `σ`. Establish `hu : ∀ y : M, IsUnit ((σ : D →+* K) y)`.

Introduce and unpack `⟨_, m, hm, rfl⟩`. Rewrite using `[AlgHom.coe_toRingHom, AlgHom.commutes]`. Conclude with `isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))`. Set `τ₀ : L →+* K` to `IsLocalization.lift hu`. Establish `hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K`.

Apply `IsLocalization.ringHom_ext O⁰` to reduce the goal to its premises. Use extensionality with `c`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]`. Simplify using the standard rewrite rules.

Use `⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩` and prove the remaining obligations. Use extensionality with `d`. Simplify using `[r, τ₀, IsLocalization.lift_eq]`. Use `letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj`. Use `⟨inst, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]`. Conclude with `Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)`.
-/
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

/- English proof (translation)
Introduce `O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha`. Establish `: Module.Free O D` using `inferInstance`. Take `⟨hF, hN⟩` from `algebra_norm_eq_prod_embeddings (O := O) (K := K) a`. Establish `hn : Algebra.norm O a ≠ 0` using `Algebra.norm_ne_zero_iff.2 ha`. Establish `hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0` using `fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))`.

Establish `h1 : v 1 = 0`. Use `hv.mul 1 1 one_ne_zero one_ne_zero` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a)`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using h1`. Consider the case `insert τ s hτ ih`. Rewrite using `[Finset.prod_insert hτ, Finset.sum_insert hτ, hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]`.

Rewrite using `[length_quotient_eq_norm_valuation]`. Use `⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩` and prove the remaining obligations. Rewrite using `[← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]`.
-/
theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
