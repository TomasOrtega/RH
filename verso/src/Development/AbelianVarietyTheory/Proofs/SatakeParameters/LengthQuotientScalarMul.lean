import Mathlib
open Pointwise

namespace GlobalTheory

/- English proof (translation)
Introduce `O M _ _ _ _ _ _ a`. Use `set d := Module.finrank O M`. Set `e : M ≃ₗ[O] (Fin d → O)` to `(Module.finBasis O M).equivFun`. Establish `hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O)) = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O))`. Use extensionality with `x`.

Simplify using `only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.smul_apply, LinearMap.id_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩ i`. Rewrite using `[LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)`.

Introduce `h choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)`. Use `⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[← hc i, mul_comm]`.

Set `f` to `(Submodule.Quotient.equiv _ _ e hmap).trans (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))`. Rewrite using `[f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.
-/
theorem length_quot_smul_range_finite_free : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O M _ _ _ _ _ _ a
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end GlobalTheory
