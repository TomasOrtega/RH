import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct

namespace GlobalTheory.AdelicComp

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Establish `h : compAt L w (x ⊗ₜ a) = x ⊗ₜ evalAt L w a` using `rfl`. Rewrite using `[h]`.

Simplify using `only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem coord_compAt (L : Type) [Field L] [NumberField L] [IsCMField L] {ι : Type} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι (maximalRealSubfield L) L)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i : ι) (z : AL L) :
    TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ (compAt L w z))
      = evalAt L w (TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    have h : compAt L w (x ⊗ₜ a) = x ⊗ₜ evalAt L w a := rfl
    rw [h]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x a`. Simplify using `only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]`. Consider the case `add x y hx hy`.

Simplify using `only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]`. Rewrite using `[← hx, ← hy]`.
-/
theorem eq_sum_coord {K V M : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (z : V ⊗[K] M) :
    z = ∑ i, b i ⊗ₜ[K] TensorProduct.lid K M ((b.coord i).rTensor M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]

/- English proof (translation)
Introduce `L _ _ _ z hz`. Set `b` to `Module.finBasis (maximalRealSubfield L) L`. Rewrite using `[eq_sum_coord b z]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `: TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z) = 0`.

Use `Subtype.ext (funext fun w => ?_)` and prove the remaining obligations. Establish `h` using `coord_compAt L b w i z`. Rewrite `h` using `[hz w, map_zero, map_zero]`. Conclude with `h.symm`. Rewrite using `[this, TensorProduct.tmul_zero]`.
-/
theorem eq_zero_of_compAt_eq_zero :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (z : AL L), (∀ w, compAt L w z = 0) → z = 0 := by
  intro L _ _ _ z hz
  classical
  let b := Module.finBasis (maximalRealSubfield L) L
  rw [eq_sum_coord b z]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : TensorProduct.lid (maximalRealSubfield L) _ ((b.coord i).rTensor _ z) = 0 := by
    refine Subtype.ext (funext fun w => ?_)
    have h := coord_compAt L b w i z
    rw [hz w, map_zero, map_zero] at h
    exact h.symm
  rw [this, TensorProduct.tmul_zero]

end GlobalTheory.AdelicComp
