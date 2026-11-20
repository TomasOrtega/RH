import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.RelBaseChangeSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial TensorProduct

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p s hp => simp only [map_mul, hp, map_X, aeval_X]`.
-/
theorem RelBaseChange.aeval_map {F F' : Type} [Field F] [Field F'] [Algebra F F'] {σ τ : Type}
    (g : σ → MvPolynomial τ F) (p : MvPolynomial σ F) :
    aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (MvPolynomial.map (algebraMap F F') p) =
      MvPolynomial.map (algebraMap F F') (aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, map_X, aeval_X]

/- English proof (translation)
Introduce `F F' _ _ _ σ τ g`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `p hp`. Rewrite `hp` using `[RingHom.mem_ker]`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Use `erw [RelBaseChange.aeval_map g p, hp, map_zero]`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Set `Φ : MvPolynomial σ F →ₗ[F] MvPolynomial τ F` to `(aeval g).toLinearMap`.

Set `eσ` to `MvPolynomial.algebraTensorAlgEquiv (σ := σ) F F'`. Set `eτ` to `MvPolynomial.algebraTensorAlgEquiv (σ := τ) F F'`. Establish `key : ∀ y : F' ⊗[F] MvPolynomial σ F, eτ (AlgebraTensorModule.lTensor F' F' Φ y) = aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (eσ y)`. Introduce `y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Consider the case `tmul a p`. Simplify using `only [AlgebraTensorModule.lTensor_tmul, eσ, eτ, algebraTensorAlgEquiv_tmul, map_smul, RelBaseChange.aeval_map, Φ, AlgHom.toLinearMap_apply]`. Establish `hy : eσ.symm x ∈ LinearMap.ker (AlgebraTensorModule.lTensor F' F' Φ)`.

Rewrite using `[LinearMap.mem_ker]`. Apply `eτ.injective` to reduce the goal to its premises. Rewrite using `[key, AlgEquiv.apply_symm_apply, hx, map_zero]`. Rewrite `hy` using `[Module.Flat.ker_lTensor_eq]`. Take `⟨z, hz⟩` from `hy`.

Establish `hx' : x = eσ (AlgebraTensorModule.lTensor F' F' (LinearMap.ker Φ).subtype z)`. Rewrite using `[hz, AlgEquiv.apply_symm_apply]`. Rewrite using `[hx']`. Use `clear hz hx'`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add y z hy hz => rw [map_add, map_add]`. Conclude with `Ideal.add_mem _ hy hz`. Consider the case `tmul a k`. Simplify using `only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, eσ, algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]`.

Use `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker]`. Conclude with `k.2`.
-/
theorem RelBaseChange.proof : RelBaseChange.Statement := by
  intro F F' _ _ _ σ τ g
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    erw [RelBaseChange.aeval_map g p, hp, map_zero]
  · intro x hx
    rw [RingHom.mem_ker] at hx
    let Φ : MvPolynomial σ F →ₗ[F] MvPolynomial τ F := (aeval g).toLinearMap
    let eσ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F F'
    let eτ := MvPolynomial.algebraTensorAlgEquiv (σ := τ) F F'
    have key : ∀ y : F' ⊗[F] MvPolynomial σ F,
        eτ (AlgebraTensorModule.lTensor F' F' Φ y) =
          aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (eσ y) := by
      intro y
      induction y with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a p =>
        simp only [AlgebraTensorModule.lTensor_tmul, eσ, eτ, algebraTensorAlgEquiv_tmul, map_smul,
          RelBaseChange.aeval_map, Φ, AlgHom.toLinearMap_apply]
    have hy : eσ.symm x ∈ LinearMap.ker (AlgebraTensorModule.lTensor F' F' Φ) := by
      rw [LinearMap.mem_ker]
      apply eτ.injective
      rw [key, AlgEquiv.apply_symm_apply, hx, map_zero]
    rw [Module.Flat.ker_lTensor_eq] at hy
    obtain ⟨z, hz⟩ := hy
    have hx' : x = eσ (AlgebraTensorModule.lTensor F' F' (LinearMap.ker Φ).subtype z) := by
      rw [hz, AlgEquiv.apply_symm_apply]
    rw [hx']
    clear hz hx'
    induction z with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add]; exact Ideal.add_mem _ hy hz
    | tmul a k =>
      simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, eσ,
        algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      exact k.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
