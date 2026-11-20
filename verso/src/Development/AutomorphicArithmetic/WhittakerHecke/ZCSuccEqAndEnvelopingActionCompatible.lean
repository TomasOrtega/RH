import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ZSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

/- English proof (translation)
Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `f`. Establish `hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0`. Apply `Polynomial.funext` to reduce the goal to its premises. Introduce `u`.

Use `congrArg f (h u)` as an intermediate fact. Simplify using `only [map_sum, map_smul, map_zero, smul_eq_mul] at this`. Simplify using `only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.

Use `congrArg (fun p => Polynomial.coeff p (n - (i + 1))) hp` as an intermediate fact. Simplify using `only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this`. Rewrite `this` using `[Finset.sum_eq_single i]`. Simplify using `using this`. Introduce `j _ hj`.

Rewrite using `[if_neg]`. Introduce `e`. Apply `hj` to reduce the goal to its premises. Use `j.2` as an intermediate fact. Use `i.2` as an intermediate fact.

Conclude with `Fin.ext (by omega)`. Simplify using the standard rewrite rules.
-/
private theorem UpperTheory.polynomial_identity_coefficients_zero {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => Polynomial.coeff p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `UpperTheory.polynomial_identity_coefficients_zero (fun i : Fin n => a (i + 1) - b i) (fun u => ?_) i` and prove the remaining obligations. Use `h u` as an intermediate fact. Rewrite `this` using `[Finset.sum_range_succ', add_comm, Nat.sub_zero, add_right_inj, ← Fin.sum_univ_eq_sum_range (fun i => u ^ (n - (i + 1)) • a (i + 1)) n]`. Simplify using `only [smul_sub, Finset.sum_sub_distrib, this, sub_self]`.
-/
private theorem UpperTheory.polynomial_coefficients_compare {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (a : ℕ → M) (b : Fin n → M)
    (h : ∀ u : ℂ, ∑ i ∈ Finset.range (n + 1), u ^ (n - i) • a i = u ^ n • a 0 + ∑ i : Fin n, u ^ (n - (i + 1)) • b i)
    (i : Fin n) : a (i + 1) = b i := by
  rw [← sub_eq_zero]
  refine UpperTheory.polynomial_identity_coefficients_zero (fun i : Fin n => a (i + 1) - b i) (fun u => ?_) i
  have := h u
  rw [Finset.sum_range_succ', add_comm, Nat.sub_zero, add_right_inj,
    ← Fin.sum_univ_eq_sum_range (fun i => u ^ (n - (i + 1)) • a (i + 1)) n] at this
  simp only [smul_sub, Finset.sum_sub_distrib, this, sub_self]

/- English proof (translation)
Introduce `E _ _ _ n`. Use `⟨fun τ i => ?_, fun u φ => ?_⟩` and prove the remaining obligations. Take `⟨h0, h1⟩` from `UpperTheory.ConvolutionTheory.BW.zSpec E n τ`. Use `UpperTheory.polynomial_coefficients_compare (M := UC E n) (UpperTheory.ConvolutionTheory.BW.zC E n τ) (zc τ) (fun u => ?_) i` and prove the remaining obligations. Rewrite using `[h0]`.

Conclude with `(h1 u).symm.trans ((UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2 u)`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Both sides reduce to the same expression. Consider the case `tmul c x`.

Establish `e : uAct (TensorProduct.tmul ℝ c x : UC E n) = c • uAction x` using `(Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uAction x)).symm`. Rewrite using `[UpperTheory.V.Cm.uC_tmul, e]`. Both sides reduce to the same expression. Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, ha, hb]`.
-/
theorem UpperTheory.zC_succ_eq_and_envelopingAction_compatible :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ),
          (∀ (τ : E →+* ℂ) (i : Fin n), UpperTheory.ConvolutionTheory.BW.zC E n τ (i + 1) = zc τ i) ∧
          ∀ (u : UC E n) (φ : GlobalTheory.CuspRep.Sm E n), (UpperTheory.V.Cm.uC E n u φ).1 = (uAct u (UpperTheory.V.Cm.smEq E n φ)).1 := by
  intro E _ _ _ n
  refine ⟨fun τ i => ?_, fun u φ => ?_⟩
  · obtain ⟨h0, h1⟩ := UpperTheory.ConvolutionTheory.BW.zSpec E n τ
    refine UpperTheory.polynomial_coefficients_compare (M := UC E n) (UpperTheory.ConvolutionTheory.BW.zC E n τ) (zc τ) (fun u => ?_) i
    rw [h0]
    exact (h1 u).symm.trans ((UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2 u)
  · induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul c x =>
      have e : uAct (TensorProduct.tmul ℝ c x : UC E n) = c • uAction x :=
        (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uAction x)).symm
      rw [UpperTheory.V.Cm.uC_tmul, e]
      rfl
    | add a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, ha, hb]
