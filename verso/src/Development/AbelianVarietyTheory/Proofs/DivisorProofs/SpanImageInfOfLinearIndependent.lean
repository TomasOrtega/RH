import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `haveI := Fintype.ofFinite ι`. Set `B` to `Algebra.TensorProduct.basis ℂ b`. Set `J : ℂ ⊗[K] V →ₗ[ℂ] W` to `B.constr ℂ (fun k => j (b k))`. Establish `hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k)` using `fun k => by`.

Use `B.constr_basis ℂ (fun k => j (b k)) k` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.basis_apply]`. Then use the resulting hypothesis. Establish `hJ : ∀ v, J (1 ⊗ₜ v) = j v` using `fun v => by`. Rewrite using `[← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul, ← algebraMap_smul ℂ (b.repr v k)]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective J`. Apply `Module.Basis.injective_constr_of_linearIndependent` to reduce the goal to its premises. Conclude with `hb`.

Establish `key : ∀ A : Submodule K V, Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J` using `fun A => by`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun v _ => (hJ v).symm`. Rewrite using `[key, key, key, baseChange_inf, Submodule.map_inf _ hinj]`.
-/
theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by
    rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
