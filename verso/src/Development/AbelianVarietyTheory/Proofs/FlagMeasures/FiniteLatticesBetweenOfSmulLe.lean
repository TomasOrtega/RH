import Mathlib
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
open NumberField

namespace GlobalTheory

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ M hM N hN`. Establish `hNK : (N : K) ≠ 0` using `by exact_mod_cast hN.ne'`. Set `f : V →ₗ[𝓞 K] V` to `(((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)`. Establish `hf : ∀ x, f x = (N : K)⁻¹ • x` using `fun x => rfl`. Establish `hback : ∀ x : V, f ((N : K) • x) = x`.

Introduce `x`. Rewrite using `[hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]`. Establish `hsm : ∀ x ∈ M, (N : K) • x ∈ M`. Introduce `x hx`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `nsmul_mem hx N`. Use `set D := M.map f with hD`. Establish `hMD : M ≤ D` using `fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩`. Establish `hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆ {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D}`. Introduce and unpack `Λ ⟨h1, h2⟩`.

Conclude with `⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩`. Use `Set.Finite.subset ?_ hsub` and prove the remaining obligations. Establish `h1` using `Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_`. Use `Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_) (Submodule.toAddSubgroup_injective.injOn)` and prove the remaining obligations. Introduce and unpack `_ ⟨Λ, ⟨h2, h3⟩, rfl⟩`.

Conclude with `⟨h2, h3⟩`. Establish `f1 : Module.Finite (𝓞 K) D` using `Module.Finite.iff_fg.mpr (hM.map f)`. Establish `f2 : Module.Finite ℤ D` using `Module.Finite.trans (𝓞 K) D`. Establish `f3 : AddGroup.FG D.toAddSubgroup` using `Module.Finite.iff_addGroup_fg.mp f2`. Apply `AddCommGroup.finite_of_fg_isAddTorsion` to reduce the goal to its premises.

Introduce `x`. Proceed by induction on `x using QuotientAddGroup.induction_on with`. Consider the case `H q`. Rewrite using `[isOfFinAddOrder_iff_zsmul_eq_zero]`. Use `⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Take `⟨m, hm, hq⟩` from `q.2`. Establish `: (((N : ℤ) • q : D.toAddSubgroup) : V) = m`. Rewrite using `[AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast, smul_smul, mul_inv_cancel₀ hNK, one_smul]`. Rewrite using `[this]`.

Conclude with `hm`.
-/
theorem finite_lattices_between_of_smul_le :
    ∀ {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), M.FG → ∀ N : ℕ, 0 < N →
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M}.Finite := by
  intro K V _ _ _ _ _ _ M hM N hN
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  let f : V →ₗ[𝓞 K] V := (((N : K)⁻¹) • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K)
  have hf : ∀ x, f x = (N : K)⁻¹ • x := fun x => rfl
  have hback : ∀ x : V, f ((N : K) • x) = x := by
    intro x; rw [hf, smul_smul, inv_mul_cancel₀ hNK, one_smul]
  have hsm : ∀ x ∈ M, (N : K) • x ∈ M := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx N
  set D := M.map f with hD
  have hMD : M ≤ D := fun x hx => ⟨(N : K) • x, hsm x hx, hback x⟩
  have hsub : {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ ∀ x ∈ Λ, (N : K) • x ∈ M} ⊆
      {Λ : Submodule (𝓞 K) V | M ≤ Λ ∧ Λ ≤ D} := by
    rintro Λ ⟨h1, h2⟩
    exact ⟨h1, fun x hx => ⟨(N : K) • x, h2 x hx, hback x⟩⟩
  refine Set.Finite.subset ?_ hsub
  have h1 := Formalism.HermitianLatticesTheory.final_finIntermediate V M.toAddSubgroup D.toAddSubgroup hMD ?_
  · refine Set.Finite.of_finite_image (f := Submodule.toAddSubgroup) (h1.subset ?_)
      (Submodule.toAddSubgroup_injective.injOn)
    rintro _ ⟨Λ, ⟨h2, h3⟩, rfl⟩
    exact ⟨h2, h3⟩
  · have f1 : Module.Finite (𝓞 K) D := Module.Finite.iff_fg.mpr (hM.map f)
    have f2 : Module.Finite ℤ D := Module.Finite.trans (𝓞 K) D
    have f3 : AddGroup.FG D.toAddSubgroup := Module.Finite.iff_addGroup_fg.mp f2
    apply AddCommGroup.finite_of_fg_isAddTorsion
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      rw [isOfFinAddOrder_iff_zsmul_eq_zero]
      refine ⟨(N : ℤ), by exact_mod_cast hN.ne', ?_⟩
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      obtain ⟨m, hm, hq⟩ := q.2
      have : (((N : ℤ) • q : D.toAddSubgroup) : V) = m := by
        rw [AddSubgroup.coe_zsmul, ← hq, hf, ← Int.cast_smul_eq_zsmul K, Int.cast_natCast,
          smul_smul, mul_inv_cancel₀ hNK, one_smul]
      rw [this]
      exact hm

end GlobalTheory
