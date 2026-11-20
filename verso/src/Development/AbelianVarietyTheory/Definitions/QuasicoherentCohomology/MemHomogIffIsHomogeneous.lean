import Mathlib

open TensorProduct Module
open scoped DirectSum

namespace GlobalTheory
namespace SymAlg

variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

def map (f : M →ₗ[R] M') : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M' :=
  SymmetricAlgebra.lift (SymmetricAlgebra.ι R M' ∘ₗ f)

/- English proof (translation)
Simplify using `[map]`.
-/
@[simp] theorem map_ι (f : M →ₗ[R] M') (m : M) :
    map f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R M' (f m) := by
  simp [map]

/- English proof (translation)
Use extensionality with `m`. Simplify using the standard rewrite rules.
-/
@[simp] theorem map_id : map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ := by
  ext m; simp

/- English proof (translation)
Use extensionality with `m`. Simplify using the standard rewrite rules.
-/
theorem map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map (g ∘ₗ f) = (map g).comp (map f) := by
  ext m; simp

variable (R M) in

def homog (d : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ d

/- English proof (translation)
Simplify `LinearMap.mem_range_self _ m` using `only [homog, pow_one]`.
-/
theorem ι_mem_homog (m : M) : SymmetricAlgebra.ι R M m ∈ homog R M 1 := by
  simpa only [homog, pow_one] using LinearMap.mem_range_self _ m

instance gradedMonoid : SetLike.GradedMonoid (homog R M) :=
  Submodule.nat_power_gradedMonoid _

variable (R M) in

def gradedι : M →ₗ[R] ⨁ i : ℕ, homog R M i :=
  DirectSum.lof R ℕ (fun i => homog R M i) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ ι_mem_homog

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gradedι_apply (m : M) :
    gradedι R M m = DirectSum.of (fun i : ℕ => homog R M i) 1
      ⟨SymmetricAlgebra.ι R M m, ι_mem_homog m⟩ := rfl

instance gradedAlgebra : GradedAlgebra (homog R M) :=
  GradedAlgebra.ofAlgHom _ (SymmetricAlgebra.lift (gradedι R M))
    (by
      ext m
      change DirectSum.coeAlgHom (homog R M)
        (SymmetricAlgebra.lift (gradedι R M) (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
      rw [SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.coeAlgHom_of])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/- English proof (translation)
Establish `h1 : (LinearMap.range (SymmetricAlgebra.ι R M)).map φ.toLinearMap ≤ P`. Introduce and unpack `_ ⟨_, ⟨m, rfl⟩, rfl⟩`. Conclude with `h m`. Establish `h2` using `Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M)) φ d`. Establish `h3 : φ x ∈ ((LinearMap.range (SymmetricAlgebra.ι R M)) ^ d).map φ.toLinearMap` using `⟨x, hx, rfl⟩`.

Rewrite `h3` using `[h2]`. Conclude with `pow_le_pow_left' h1 d h3`.
-/
theorem algHom_mem_pow {A : Type*} [CommRing A] [Algebra R A]
    (φ : SymmetricAlgebra R M →ₐ[R] A) (P : Submodule R A)
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) ∈ P) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : φ x ∈ P ^ d := by
  have h1 : (LinearMap.range (SymmetricAlgebra.ι R M)).map φ.toLinearMap ≤ P := by
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact h m
  have h2 := Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M)) φ d
  have h3 : φ x ∈ ((LinearMap.range (SymmetricAlgebra.ι R M)) ^ d).map φ.toLinearMap :=
    ⟨x, hx, rfl⟩
  rw [h2] at h3
  exact pow_le_pow_left' h1 d h3

/- English proof (translation)
The claim follows from `algHom_mem_pow (map f) _ (fun m => by simp) hx`.
-/
theorem map_mem_homog (f : M →ₗ[R] M') {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : map f x ∈ homog R M' d :=
  algHom_mem_pow (map f) _ (fun m => by simp) hx

/- English proof (translation)
Proceed by induction on `hx using Submodule.pow_induction_on_left' with`. Consider the case `algebraMap r => simp`. Consider the case `add x y i hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, mul_add]`. Consider the case `mem_mul m hm i x hx ih`. Take `⟨_, rfl⟩` from `hm`.

Rewrite using `[map_mul, map_mul, ih, h, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem algHom_eq_pow_mul {A : Type*} [CommRing A] [Algebra R A]
    (φ ψ : SymmetricAlgebra R M →ₐ[R] A) (s : A)
    (h : ∀ m, φ (SymmetricAlgebra.ι R M m) = s * ψ (SymmetricAlgebra.ι R M m)) {d : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ homog R M d) : φ x = s ^ d * ψ x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, mul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨_, rfl⟩ := hm
    rw [map_mul, map_mul, ih, h, pow_succ]; ring

/- English proof (translation)
Rewrite using `[← MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.homogeneousSubmodule_one_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `algHom_mem_pow (SymmetricAlgebra.equivMvPolynomial b).toAlgHom _ (fun m => ?_) hx` and prove the remaining obligations. Establish `hm : m ∈ Submodule.span R (Set.range b)` using `by rw [b.span_eq]; trivial`.

Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Simplify using `using MvPolynomial.isHomogeneous_X R i`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy`. Consider the case `smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx`. Introduce `hx`. Establish `h1 : (MvPolynomial.homogeneousSubmodule ι R 1).map (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap ≤ LinearMap.range (SymmetricAlgebra.ι R M)`. Rewrite using `[MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨b i, by simp⟩`. Establish `h2` using `Submodule.map_pow (MvPolynomial.homogeneousSubmodule ι R 1) (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom d`. Establish `h3 : x ∈ ((MvPolynomial.homogeneousSubmodule ι R 1) ^ d).map (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap` using `⟨_, hx, by simp⟩`. Rewrite `h3` using `[h2]`.

Conclude with `pow_le_pow_left' h1 d h3`.
-/
theorem mem_homog_iff_isHomogeneous {ι : Type*} (b : Basis ι R M) (d : ℕ)
    (x : SymmetricAlgebra R M) :
    x ∈ homog R M d ↔ (SymmetricAlgebra.equivMvPolynomial b x).IsHomogeneous d := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, ← MvPolynomial.homogeneousSubmodule_one_pow]
  constructor
  · intro hx
    refine algHom_mem_pow (SymmetricAlgebra.equivMvPolynomial b).toAlgHom _ (fun m => ?_) hx
    have hm : m ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simpa using MvPolynomial.isHomogeneous_X R i
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul r x _ hx => simpa only [map_smul] using Submodule.smul_mem _ r hx
  · intro hx
    have h1 : (MvPolynomial.homogeneousSubmodule ι R 1).map
        (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap ≤
        LinearMap.range (SymmetricAlgebra.ι R M) := by
      rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨b i, by simp⟩
    have h2 := Submodule.map_pow (MvPolynomial.homogeneousSubmodule ι R 1)
      (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom d
    have h3 : x ∈ ((MvPolynomial.homogeneousSubmodule ι R 1) ^ d).map
        (SymmetricAlgebra.equivMvPolynomial b).symm.toAlgHom.toLinearMap :=
      ⟨_, hx, by simp⟩
    rw [h2] at h3
    exact pow_le_pow_left' h1 d h3

instance projective [Module.Projective R M] : Module.Projective R (SymmetricAlgebra R M) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective R M›
  refine Module.Projective.of_split (map s).toLinearMap
    (map (Finsupp.linearCombination R id)).toLinearMap ?_
  rw [← AlgHom.comp_toLinearMap, ← map_comp, hs, map_id]
  rfl

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]

variable (S) in

def mapOver (j : M →ₗ[R] W) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra S W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι S W).restrictScalars R ∘ₗ j)

/- English proof (translation)
Simplify using `[mapOver]`.
-/
@[simp] theorem mapOver_ι (j : M →ₗ[R] W) (m : M) :
    mapOver S j (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S W (j m) := by
  simp [mapOver]

variable (S) in

noncomputable def baseChangeHom (j : M →ₗ[R] W) :
    S ⊗[R] SymmetricAlgebra R M →ₐ[S] SymmetricAlgebra S W :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (mapOver S j) (fun _ _ => Commute.all _ _)

/- English proof (translation)
Simplify using `[baseChangeHom, Algebra.smul_def, Algebra.ofId_apply]`.
-/
@[simp] theorem baseChangeHom_tmul (j : M →ₗ[R] W) (s : S) (x : SymmetricAlgebra R M) :
    baseChangeHom S j (s ⊗ₜ x) = s • mapOver S j x := by
  simp [baseChangeHom, Algebra.smul_def, Algebra.ofId_apply]

noncomputable def baseChangeEquiv {j : M →ₗ[R] W} (h : IsBaseChange S j) :
    S ⊗[R] SymmetricAlgebra R M ≃ₐ[S] SymmetricAlgebra S W :=
  AlgEquiv.ofAlgHom (baseChangeHom S j)
    (SymmetricAlgebra.lift
      (h.lift ((TensorProduct.mk R S (SymmetricAlgebra R M) 1) ∘ₗ SymmetricAlgebra.ι R M)))
    (by
      refine SymmetricAlgebra.algHom_ext (h.algHom_ext _ _ fun m => ?_)
      simp [h.lift_eq])
    (by
      ext m
      simp [h.lift_eq, Algebra.TensorProduct.one_def])

/- English proof (translation)
The claim follows from `baseChangeHom_tmul j s x`.
-/
@[simp] theorem baseChangeEquiv_tmul {j : M →ₗ[R] W} (h : IsBaseChange S j) (s : S)
    (x : SymmetricAlgebra R M) : baseChangeEquiv h (s ⊗ₜ x) = s • mapOver S j x :=
  baseChangeHom_tmul j s x

/- English proof (translation)
Set `Φ : S ⊗[R] Dual R M →ₗ[S] Dual S W` to `h.toDual.liftBaseChange S`. Set `e` to `lTensorHomEquivHomLTensor R M S R`. Establish `key : ∀ (t : S ⊗[R] Dual R M) (m : M), Φ t (j m) = TensorProduct.rid R S (e t m)`. Introduce `t m`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul s ξ`. Simplify using `[Φ, e, h.toDual_comp_apply, Algebra.smul_def, mul_comm]`. Use `IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩) (fun ξ => by change Φ _ = _; simp [Φ])` and prove the remaining obligations.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `t ht`. Apply `e.injective` to reduce the goal to its premises. Use extensionality with `m`. Apply `(TensorProduct.rid R S).injective` to reduce the goal to its premises.

Rewrite using `[← key, ht]`. Simplify using the standard rewrite rules. Introduce `φ`. Use `⟨e.symm ((TensorProduct.rid R S).symm.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ j), ?_⟩` and prove the remaining obligations. Use `h.algHom_ext _ _ fun m => ?_` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using the standard rewrite rules.
-/
theorem isBaseChange_dual [Module.Finite R M] [Module.Projective R M] {j : M →ₗ[R] W}
    (h : IsBaseChange S j) : IsBaseChange S h.toDual := by
  let Φ : S ⊗[R] Dual R M →ₗ[S] Dual S W := h.toDual.liftBaseChange S
  let e := lTensorHomEquivHomLTensor R M S R
  have key : ∀ (t : S ⊗[R] Dual R M) (m : M), Φ t (j m) = TensorProduct.rid R S (e t m) := by
    intro t m
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul s ξ =>
      simp [Φ, e, h.toDual_comp_apply, Algebra.smul_def, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩)
    (fun ξ => by change Φ _ = _; simp [Φ])
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply e.injective
    ext m
    apply (TensorProduct.rid R S).injective
    rw [← key, ht]
    simp
  · intro φ
    refine ⟨e.symm ((TensorProduct.rid R S).symm.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ j), ?_⟩
    refine h.algHom_ext _ _ fun m => ?_
    rw [key]
    simp

/- English proof (translation)
Proceed by induction on `hx using Submodule.pow_induction_on_left' with`. Consider the case `algebraMap r`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply R S (SymmetricAlgebra S W)]`. Conclude with `SetLike.algebraMap_mem_graded (homog S W) _`. Consider the case `add x y i hx hy ihx ihy => rw [map_add]`.

Conclude with `Submodule.add_mem _ ihx ihy`. Consider the case `mem_mul m hm i x hx ih`. Take `⟨m, rfl⟩` from `hm`. Rewrite using `[map_mul, mapOver_ι, Nat.succ_eq_one_add]`. Conclude with `SetLike.mul_mem_graded (ι_mem_homog _) ih`.
-/
theorem mapOver_mem_homog (j : M →ₗ[R] W) {d : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ homog R M d) : mapOver S j x ∈ homog S W d := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (SymmetricAlgebra S W)]
    exact SetLike.algebraMap_mem_graded (homog S W) _
  | add x y i hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, mapOver_ι, Nat.succ_eq_one_add]
    exact SetLike.mul_mem_graded (ι_mem_homog _) ih

/- English proof (translation)
Establish `h1 : Function.Injective (Algebra.TensorProduct.includeRight : SymmetricAlgebra R M →ₐ[R] S ⊗[R] SymmetricAlgebra R M)` using `Algebra.TensorProduct.includeRight_injective hS`. Introduce `x y hxy`. Apply `h1` to reduce the goal to its premises. Apply `(baseChangeEquiv h).injective` to reduce the goal to its premises. Simplify using `using hxy`.
-/
theorem mapOver_injective [Module.Projective R M] {j : M →ₗ[R] W} (h : IsBaseChange S j)
    (hS : Function.Injective (algebraMap R S)) : Function.Injective (mapOver S j) := by
  have h1 : Function.Injective (Algebra.TensorProduct.includeRight :
      SymmetricAlgebra R M →ₐ[R] S ⊗[R] SymmetricAlgebra R M) :=
    Algebra.TensorProduct.includeRight_injective hS
  intro x y hxy
  apply h1
  apply (baseChangeEquiv h).injective
  simpa using hxy

end BaseChange

end SymAlg
end GlobalTheory
