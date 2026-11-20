import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
open Module

namespace GlobalTheory.BadCount

/- English proof (translation)
Introduce `K V ι _ _ _ _ σ N f hli hsp a a' ha`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `letI : Module K V := Module.compHom V σ`. Use `haveI : IsScalarTower K ℂ V := ⟨fun k c v => by show (σ k * c) • v = σ k • c • v`. Rewrite using `[mul_smul]⟩`.

Set `g : (Fin N → K) →ₗ[K] V` to `{ toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }`. Establish `hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤`. Rewrite using `[eq_top_iff, ← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[f.map_smulₛₗ, Pi.basisFun_apply]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Set `c : Basis (Fin N) ℂ V` to `Basis.mk hli hsp'.ge`. Establish `hc : ∀ k, c k = f (Pi.single k 1)` using `fun k => Basis.mk_apply _ _ _`.

Set `e` to `(Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)`. Establish `hbc : IsBaseChange ℂ g`. Use `IsBaseChange.of_equiv e fun m => ?_` and prove the remaining obligations. Establish `h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g`. Use `(Pi.basisFun K (Fin N)).ext fun k => ?_` and prove the remaining obligations.

Use `(Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.basis_apply]`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Rewrite using `[this, Equiv.refl_apply, hc, Pi.basisFun_apply]`. Both sides reduce to the same expression.

Conclude with `congrArg (fun φ => φ m) h`. Conclude with `(finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1`.
-/
theorem finrank_iInf_ker_semilinear : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module ℂ V]
    [Finite ι] (σ : K →+* ℂ) (N : ℕ) (f : (Fin N → K) →ₛₗ[σ] V),
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ →
    ∀ (a : ι → (Fin N → K) →ₗ[K] (Fin N → K)) (a' : ι → V →ₗ[ℂ] V),
      (∀ i v, a' i (f v) = f (a i v)) →
      finrank ℂ (⨅ i, LinearMap.ker (a' i) : Submodule ℂ V) =
        finrank K (⨅ i, LinearMap.ker (a i) : Submodule K (Fin N → K)) := by
  intro K V ι _ _ _ _ σ N f hli hsp a a' ha
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Module K V := Module.compHom V σ
  haveI : IsScalarTower K ℂ V := ⟨fun k c v => by
    show (σ k * c) • v = σ k • c • v
    rw [mul_smul]⟩
  let g : (Fin N → K) →ₗ[K] V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun k x => f.map_smulₛₗ k x }
  have hsp' : Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← (Pi.basisFun K (Fin N)).sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [f.map_smulₛₗ, Pi.basisFun_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis (Fin N) ℂ V := Basis.mk hli hsp'.ge
  have hc : ∀ k, c k = f (Pi.single k 1) := fun k => Basis.mk_apply _ _ _
  let e := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv c (Equiv.refl _)
  have hbc : IsBaseChange ℂ g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h : (e.toLinearMap.restrictScalars K ∘ₗ TensorProduct.mk K ℂ (Fin N → K) 1) = g := by
      refine (Pi.basisFun K (Fin N)).ext fun k => ?_
      have := (Algebra.TensorProduct.basis ℂ (Pi.basisFun K (Fin N))).equiv_apply k c (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hc, Pi.basisFun_apply]
      rfl
    exact congrArg (fun φ => φ m) h
  exact (finrank_iInf_ker_baseChange K ℂ (Fin N → K) V ι g hbc a a' ha).1

end GlobalTheory.BadCount
