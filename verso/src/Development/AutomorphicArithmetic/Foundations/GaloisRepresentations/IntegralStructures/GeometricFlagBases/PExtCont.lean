import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simpa using continuous_const`. Consider the case `add x y hx hy`. Simplify using `only [map_add]`.

Conclude with `hx.add hy`. Consider the case `tmul l m`. Set `b` to `Module.finBasis F M`. Establish `key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) = ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i)`. Introduce `g`.

Rewrite using `[LinearMap.baseChange_tmul]`. Use `conv_lhs => rw [← b.sum_repr (a g m)]`. Rewrite using `[TensorProduct.tmul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[key]`. Conclude with `continuous_finset_sum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const`.
-/
theorem UpperTheory.Gal.Int.Geo.extCont_of :
    ExtCont := by
  intro Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | add x y hx hy =>
    simp only [map_add]
    exact hx.add hy
  | tmul l m =>
    let b := Module.finBasis F M
    have key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) =
        ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i) := by
      intro g
      rw [LinearMap.baseChange_tmul]
      conv_lhs => rw [← b.sum_repr (a g m)]
      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]
      rfl
    simp_rw [key]
    exact continuous_finset_sum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const
