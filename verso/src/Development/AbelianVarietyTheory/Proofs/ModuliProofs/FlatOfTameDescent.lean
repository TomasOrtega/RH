import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

open scoped TensorProduct

namespace GlobalTheory

namespace TameFlat

open TensorProduct

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c r`. Simplify using `only [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.restrictScalars_apply, map_smul]`. Consider the case `add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]`. Consider the case `add s u hs hu => simp only [map_add, hs, hu]`.
-/
theorem cancel_natural {A B R X Y : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R]
    [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]
    (f : X →ₗ[B] Y) (t : X ⊗[B] (B ⊗[A] R)) :
    AlgebraTensorModule.cancelBaseChange A B B Y R (f.rTensor _ t) =
      (f.restrictScalars A).rTensor R (AlgebraTensorModule.cancelBaseChange A B B X R t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      simp only [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
        LinearMap.restrictScalars_apply, map_smul]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add s u hs hu => simp only [map_add, hs, hu]

/- English proof (translation)
Rewrite using `[Module.Flat.iff_rTensor_injective']`. Introduce `I`. Establish `hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Introduce `c`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]`. Conclude with `I.mul_mem_right _ ha`.

Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro c`. Rewrite using `[mul_add, map_add]`. Conclude with `I.add_mem (hx c) (hy c)`.

Consider the case `smul d x _ hx => intro c`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hx (c * d)`. Use `set J : Ideal B := I.map (algebraMap A B)`. Set `eJ : J →ₗ[A] I` to `LinearMap.codRestrict (I.restrictScalars A) (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)`.

Establish `heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id`. Use extensionality with `i`. Express the relevant statement in the definitionally equal form `e (algebraMap A B (i : A)) = (i : A)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]`. Set `Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R)` to `(AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ TensorProduct.map (Algebra.idealMap B I) LinearMap.id`.

Set `Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R` to `TensorProduct.map eJ LinearMap.id ∘ₗ (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A`. Establish `hΨΦ : ∀ x, Ψ (Φ x) = x`. Introduce `x`. Establish `: Ψ ∘ₗ Φ = LinearMap.id`. Apply `TensorProduct.ext'` to reduce the goal to its premises.

Introduce `i r`. Simplify using `only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`. Rewrite using `[← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]`. Conclude with `congrArg (fun f => f x) this`. Establish `hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype)` using `Module.Flat.iff_rTensor_injective'.mp inferInstance J`.

Establish `hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) = (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x)`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul i r`.

Simplify using `only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul, Submodule.subtype_apply, TensorProduct.lid_tmul]`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `algebraMap A B (i : A) ⊗ₜ[A] r = _`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]`.

Introduce `x y hxy`. Establish `h1 : Φ x = Φ y`. Apply `hinc` to reduce the goal to its premises. Apply `(TensorProduct.lid B (B ⊗[A] R)).injective` to reduce the goal to its premises. Rewrite using `[hkey, hkey, hxy]`.

Rewrite using `[← hΨΦ x, ← hΨΦ y, h1]`.
-/
theorem flat_of_retraction {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  have hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact I.mul_mem_right _ ha
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add]; exact I.add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  set J : Ideal B := I.map (algebraMap A B)

  let eJ : J →ₗ[A] I := LinearMap.codRestrict (I.restrictScalars A)
    (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)
  have heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id := by
    ext i
    change e (algebraMap A B (i : A)) = (i : A)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]

  let Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R) :=
    (AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.map (Algebra.idealMap B I) LinearMap.id
  let Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R :=
    TensorProduct.map eJ LinearMap.id ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    have : Ψ ∘ₗ Φ = LinearMap.id := by
      apply TensorProduct.ext'
      intro i r
      simp only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]
    exact congrArg (fun f => f x) this
  have hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance J

  have hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) =
      (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul i r =>
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change algebraMap A B (i : A) ⊗ₜ[A] r = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, TensorProduct.tmul_add]
  intro x y hxy
  have h1 : Φ x = Φ y := by
    apply hinc
    apply (TensorProduct.lid B (B ⊗[A] R)).injective
    rw [hkey, hkey, hxy]
  rw [← hΨΦ x, ← hΨΦ y, h1]

/- English proof (translation)
Establish `: Fintype Γ` using `Fintype.ofFinite Γ`. Rewrite `hb` using `[finsum_eq_sum_of_fintype]`. Establish `hfix : ∀ x : B, ∃ a : A, algebraMap A B a = ∑ g : Γ, g • (b * x)`. Introduce `x`. Apply `Algebra.IsInvariant.isInvariant (G := Γ)` to reduce the goal to its premises.

Introduce `h`. Rewrite using `[Finset.smul_sum]`. Repeatedly rewrite using `[← mul_smul]`. Conclude with `Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • (b * x))`. Use `choose f hf using hfix`.

Use `⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `x y`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_add, hf, hf, hf, ← Finset.sum_add_distrib]`. Repeatedly rewrite using `[mul_add, smul_add]`.

Introduce `a x`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, ← Algebra.smul_def, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_comm]`.

Use `show f 1 = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hf, mul_one, map_one, hb]`.
-/
theorem exists_retraction {Γ A B : Type} [Group Γ] [Finite Γ] [CommRing A] [CommRing B]
    [MulSemiringAction Γ B] [Algebra A B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ]
    (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : ∑ᶠ g : Γ, g • b = 1) :
    ∃ e : B →ₗ[A] A, e 1 = 1 := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [finsum_eq_sum_of_fintype] at hb
  have hfix : ∀ x : B, ∃ a : A, algebraMap A B a = ∑ g : Γ, g • (b * x) := by
    intro x
    apply Algebra.IsInvariant.isInvariant (G := Γ)
    intro h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • (b * x))
  choose f hf using hfix
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply hinj
    rw [map_add, hf, hf, hf, ← Finset.sum_add_distrib]
    simp_rw [mul_add, smul_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, ← Algebra.smul_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_smul_comm, smul_comm]
  · show f 1 = 1
    apply hinj
    rw [hf, mul_one, map_one, hb]

end TameFlat

/- English proof (translation)
Introduce `Γ _ _ A B R C`. Use `intros`. Name the introduced variables `hAB _ _ hpo hflat htr`. Take `⟨b, hb⟩` from `htr`. Take `⟨e, he⟩` from `TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb`.

Establish `: Module.Flat B (B ⊗[A] R)` using `Module.Flat.of_linearEquiv hpo.out.equiv`. Conclude with `TameFlat.flat_of_retraction e he`.
-/
theorem flat_of_tame_descent :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R]
      [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R]
      [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C]
      [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ]
      [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) →
      Function.Injective (algebraMap R C) →
      (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) →
      Algebra.IsPushout A B R C → Module.Flat B C → (∃ b : B, ∑ᶠ g : Γ, g • b = 1) →
      Module.Flat A R := by
  intro Γ _ _ A B R C
  intros
  rename_i hAB _ _ hpo hflat htr
  obtain ⟨b, hb⟩ := htr
  obtain ⟨e, he⟩ := TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb
  have : Module.Flat B (B ⊗[A] R) := Module.Flat.of_linearEquiv hpo.out.equiv
  exact TameFlat.flat_of_retraction e he

end GlobalTheory
