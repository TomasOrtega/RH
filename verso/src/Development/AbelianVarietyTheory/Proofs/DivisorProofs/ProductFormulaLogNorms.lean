import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureFinite

/- English proof (translation)
Take `⟨I, hI, Ai, hF, hA, e, hsep⟩` from `(Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance`. Use `letI : ∀ i, Algebra R (Ai i) := fun i => ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra`. Use `haveI : ∀ i, IsScalarTower R K (Ai i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `ψ : ∀ i, L →ₐ[K] Ai i` to `fun i => (Pi.evalAlgHom K Ai i).comp e.toAlgHom`. Use `haveI : ∀ i, Module.Finite K (Ai i) := fun i => Module.Finite.of_surjective (ψ i).toLinearMap (by`.

Introduce `y`. Take `⟨x, hx⟩` from `e.surjective (Pi.single i y)`. Conclude with `⟨x, by simp [ψ, hx]⟩)`. Use `haveI : ∀ i, Module.Finite R (integralClosure R (Ai i)) := fun i => IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))`. Set `φ : integralClosure R L →ₗ[R] (∀ i, integralClosure R (Ai i))` to `LinearMap.pi (fun i => (((ψ i).restrictScalars R).toLinearMap.comp (integralClosure R L).val.toLinearMap).codRestrict (integralClosure R (Ai i)).toSubmodule (fun x => IsIntegral.map ((ψ i).restrictScalars R) x.2))`.

Use `haveI : IsNoetherian R (∀ i, integralClosure R (Ai i)) := inferInstance`. Establish `hφ : Function.Injective φ`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `e.injective` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `congrArg (fun f => ((f i : integralClosure R (Ai i)) : Ai i)) h` as an intermediate fact. Conclude with `this`. Use `haveI := isNoetherian_of_injective φ hφ`. Conclude with `Module.IsNoetherian.finite R _`.
-/
theorem integralClosure_finite_of_etale (R K L : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Module.Finite K L]
    [Algebra.Etale K L] : Module.Finite R (integralClosure R L) := by
  classical
  obtain ⟨I, hI, Ai, hF, hA, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K L).mp inferInstance
  letI : ∀ i, Algebra R (Ai i) := fun i => ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K (Ai i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : ∀ i, L →ₐ[K] Ai i := fun i => (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  haveI : ∀ i, Module.Finite K (Ai i) := fun i =>
    Module.Finite.of_surjective (ψ i).toLinearMap (by
      intro y
      obtain ⟨x, hx⟩ := e.surjective (Pi.single i y)
      exact ⟨x, by simp [ψ, hx]⟩)
  haveI : ∀ i, Module.Finite R (integralClosure R (Ai i)) := fun i =>
    IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))
  let φ : integralClosure R L →ₗ[R] (∀ i, integralClosure R (Ai i)) :=
    LinearMap.pi (fun i =>
      (((ψ i).restrictScalars R).toLinearMap.comp (integralClosure R L).val.toLinearMap).codRestrict
        (integralClosure R (Ai i)).toSubmodule
        (fun x => IsIntegral.map ((ψ i).restrictScalars R) x.2))
  haveI : IsNoetherian R (∀ i, integralClosure R (Ai i)) := inferInstance
  have hφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    have := congrArg (fun f => ((f i : integralClosure R (Ai i)) : Ai i)) h
    exact this
  haveI := isNoetherian_of_injective φ hφ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite

namespace GlobalTheory.ClosureFinite

/- English proof (translation)
Introduce `A R _ _ _ _ _ _ _ hinj D _ _ _ _`. Set `GF` to `GlobalTheory.LocAcyc.GenFib A R`. Set `S` to `Algebra.algebraMapSubmonoid R (nonZeroDivisors A)`. Set `K'` to `FractionRing R`. Establish `hS : ∀ y : S, IsUnit (algebraMap R K' y)`.

Introduce and unpack `⟨y, a, ha, rfl⟩`. Apply `isUnit_iff_ne_zero.mpr` to reduce the goal to its premises. Introduce `h0`. Rewrite `h0` using `[IsFractionRing.to_map_eq_zero_iff]`. Establish `: a = 0` using `hinj (by simpa using h0)`.

Conclude with `nonZeroDivisors.ne_zero ha this`. Set `g : GF →+* K'` to `IsLocalization.lift (M := S) hS`. Use `letI : Algebra GF K' := g.toAlgebra`. Use `haveI : IsScalarTower R GF K' := IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)`. Establish `hg : Function.Injective (algebraMap GF K')`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective S x`. Express the relevant statement in the definitionally equal form `g (IsLocalization.mk' GF r s) = 0 at hx`. Use `show IsLocalization.mk' GF r s = 0`.

Rewrite `hx` using `[IsLocalization.lift_mk', mul_eq_zero]`. Break down `hx with hx | hx` into its components or cases. Rewrite `hx` using `[IsFractionRing.to_map_eq_zero_iff]`. Rewrite using `[hx, IsLocalization.mk'_zero]`. Conclude with `absurd hx (Units.ne_zero _)`.

Set `L'` to `K' ⊗[GF] D`. Set `ι : D →ₐ[GF] L'` to `Algebra.TensorProduct.includeRight`. Establish `hι : Function.Injective ι`. Establish `h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D)` using `Module.Flat.rTensor_preserves_injective_linearMap _ hg`. Introduce `x y hxy`.

Apply `(TensorProduct.lid GF D).symm.injective` to reduce the goal to its premises. Apply `h1` to reduce the goal to its premises. Simplify using `only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]`. Conclude with `hxy`. Establish `key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L'`.

Use extensionality with `r`. Use `show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L', ← IsScalarTower.algebraMap_apply R GF K']`. Use `letI inst : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) := GlobalTheory.KeyOriginNoeth.closureAlg A R D`. Set `Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L'` to `{ toFun := fun c => ⟨ι c.1, by`.

Establish `hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1` using `c.2`. Take `⟨p, hp, he⟩` from `hc`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Establish `h2` using `Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1`. Rewrite `h2` using `[he, map_zero]`.

Rewrite using `[← key]`. Conclude with `h2.symm⟩`. Use the proof step `map_add' := fun x y => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ι (x.1 + y.1) = ι x.1 + ι y.1`.

Conclude with `map_add ι _ _`. Use the proof step `map_smul' := fun r c => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1`. Rewrite using `[map_mul, Algebra.smul_def]`.

Use `congr 1`. Conclude with `RingHom.congr_fun key r }`. Establish `hΦ : Function.Injective Φ`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hι` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hxy`. Use `haveI := integralClosure_finite_of_etale R K' L'`. Use `haveI := isNoetherian_of_injective Φ hΦ`. Conclude with `Module.IsNoetherian.finite R _`.
-/
theorem closure_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  classical
  let GF := GlobalTheory.LocAcyc.GenFib A R
  let S := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let K' := FractionRing R
  have hS : ∀ y : S, IsUnit (algebraMap R K' y) := by
    rintro ⟨y, a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro h0
    rw [IsFractionRing.to_map_eq_zero_iff] at h0
    have : a = 0 := hinj (by simpa using h0)
    exact nonZeroDivisors.ne_zero ha this
  let g : GF →+* K' := IsLocalization.lift (M := S) hS
  letI : Algebra GF K' := g.toAlgebra
  haveI : IsScalarTower R GF K' :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := S) hS r).symm)
  have hg : Function.Injective (algebraMap GF K') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    change g (IsLocalization.mk' GF r s) = 0 at hx
    show IsLocalization.mk' GF r s = 0
    rw [IsLocalization.lift_mk', mul_eq_zero] at hx
    rcases hx with hx | hx
    · rw [IsFractionRing.to_map_eq_zero_iff] at hx
      rw [hx, IsLocalization.mk'_zero]
    · exact absurd hx (Units.ne_zero _)
  let L' := K' ⊗[GF] D
  let ι : D →ₐ[GF] L' := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := by
    have h1 : Function.Injective ((Algebra.linearMap GF K').rTensor D) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hg
    intro x y hxy
    apply (TensorProduct.lid GF D).symm.injective
    apply h1
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have key : (ι : D →+* L').comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = algebraMap R L' := by
    ext r
    show ι (algebraMap GF D (algebraMap R GF r)) = algebraMap R L' r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply GF K' L', IsScalarTower.algebraMap_apply R K' L',
      ← IsScalarTower.algebraMap_apply R GF K']
  letI inst : Algebra R (GlobalTheory.KeyOriginNoeth.closure A R D) := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  let Φ : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] integralClosure R L' :=
    { toFun := fun c => ⟨ι c.1, by
        have hc : (GlobalTheory.KeyOriginNoeth.baseHom A R D).IsIntegralElem c.1 := c.2
        obtain ⟨p, hp, he⟩ := hc
        refine ⟨p, hp, ?_⟩
        have h2 := Polynomial.hom_eval₂ p (GlobalTheory.KeyOriginNoeth.baseHom A R D) (ι : D →+* L') c.1
        rw [he, map_zero] at h2
        rw [← key]
        exact h2.symm⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show ι (x.1 + y.1) = ι x.1 + ι y.1
        exact map_add ι _ _
      map_smul' := fun r c => by
        apply Subtype.ext
        show ι (GlobalTheory.KeyOriginNoeth.baseHom A R D r * c.1) = r • ι c.1
        rw [map_mul, Algebra.smul_def]
        congr 1
        exact RingHom.congr_fun key r }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hxy
  haveI := integralClosure_finite_of_etale R K' L'
  haveI := isNoetherian_of_injective Φ hΦ
  exact Module.IsNoetherian.finite R _

end GlobalTheory.ClosureFinite
