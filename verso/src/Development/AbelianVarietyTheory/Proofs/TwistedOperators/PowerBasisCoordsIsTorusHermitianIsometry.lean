import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

/- English proof (translation)
Establish `hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i)` using `by conv_lhs => rw [← (powB P).sum_repr z']`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]`. Rewrite using `[hs, Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← (powB P).sum_repr z]`. Rewrite using `[Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_mul_star_eq_sum (z z' : Fld P) :
    ∑ i, ∑ j, σ ((powB P).repr z' i) * gramOne P i j * (powB P).repr z j =
      Algebra.trace E (Fld P) (z * star' P z') := by
  have hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i) := by
    conv_lhs => rw [← (powB P).sum_repr z']
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]
  rw [hs, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (powB P).sum_repr z]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]
  ring

/- English proof (translation)
Introduce `F E _ _ _ σ r P k _ _ y y'`. Simplify using `only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂`.

Simplify using `only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]`. Consider the case `tmul a z`. Proceed by induction on `y' using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂`.

Simplify using `only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]`. Consider the case `tmul a' z'`. Establish `e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e` using `fun e => rfl`. Establish `e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z'` using `rfl`. Establish `e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j` using `fun i j => rfl`.

Establish `e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w` using `fun b w => rfl`. Simplify using `only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum, trace_mul_star_eq_sum]`. Rewrite using `[mul_comm a' a]`.
-/
theorem isIsom_coordEquiv : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k],
    IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  intro F E _ _ _ σ r P k _ _ y y'
  simp only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
    | tmul a' z' =>
      have e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e := fun e => rfl
      have e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z' := rfl
      have e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j := fun i j => rfl
      have e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w := fun b w => rfl
      simp only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum,
        trace_mul_star_eq_sum]
      rw [mul_comm a' a]

end GlobalTheory.TrUnitLat
