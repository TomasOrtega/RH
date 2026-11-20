import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems
open scoped TensorProduct

/- English proof (translation)
Introduce `K _ r B`. Set `g : Bool → MvPolynomial (Fin r × Fin r) K →ₗ[K] (MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K)` to `fun b => match b with`. Consider the case `true => (Algebra.TensorProduct.includeLeft : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap`. Consider the case `false => (Algebra.TensorProduct.includeRight : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap`. Take `⟨F, hF⟩` from `KP.tensorMap (K := K) (S := Bool) (α := Fin r × Fin r) g`.

Use `⟨(TensorProduct.lift B) ∘ₗ F, ?_⟩` and prove the remaining obligations. Introduce `f f'`. Establish `h` using `hF (fun b => match b with | true => f | false => f')`. Rewrite `h` using `[Fintype.prod_bool, Fintype.prod_bool]`. Establish `h' : F (blockEmb K true f * blockEmb K false f') = f ⊗ₜ[K] f'`.

Use `h.trans ?_` and prove the remaining obligations. Use `show (f ⊗ₜ[K] (1 : MvPolynomial (Fin r × Fin r) K)) * ((1 : MvPolynomial (Fin r × Fin r) K) ⊗ₜ[K] f') = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[LinearMap.comp_apply, h', TensorProduct.lift.tmul]`.
-/
theorem bilinP : BilinP := by
  classical
  intro K _ r B
  let g : Bool → MvPolynomial (Fin r × Fin r) K →ₗ[K]
      (MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K) := fun b =>
    match b with
    | true => (Algebra.TensorProduct.includeLeft :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
    | false => (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K ⊗[K] MvPolynomial (Fin r × Fin r) K).toLinearMap
  obtain ⟨F, hF⟩ := KP.tensorMap (K := K) (S := Bool) (α := Fin r × Fin r) g
  refine ⟨(TensorProduct.lift B) ∘ₗ F, ?_⟩
  intro f f'
  have h := hF (fun b => match b with | true => f | false => f')
  rw [Fintype.prod_bool, Fintype.prod_bool] at h
  have h' : F (blockEmb K true f * blockEmb K false f') = f ⊗ₜ[K] f' := by
    refine h.trans ?_
    show (f ⊗ₜ[K] (1 : MvPolynomial (Fin r × Fin r) K)) * ((1 : MvPolynomial (Fin r × Fin r) K) ⊗ₜ[K] f') = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [LinearMap.comp_apply, h', TensorProduct.lift.tmul]

/- English proof (translation)
Introduce `A _ r e`. Prove the components needed by the constructor for the conclusion. Establish `h1 : detY A r ∈ dualWeyl A r r (qcOm r r)`. Rewrite using `[← qc_full_minor A r r le_rfl id strictMono_id rfl]`. Conclude with `qc_initMinor_mem A id le_rfl`.

Establish `h2` using `qc_pow_mem A r r _ _ h1 e`. Establish `e1 : e • qcOm r r = fun _ => e`. Use function extensionality and compare the values at `t`. Simplify using `[qcOm, t.isLt]`. Rewrite `h2` using `[e1]`. Then use the resulting hypothesis.

Introduce `l`. Unfold `detY`. Establish `hA` using `AlgHom.map_det (rowAct A (n := r) l) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))`. Establish `hM : (rowAct A (n` using `r) l).mapMatrix (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) = (C : A →+* MvPolynomial (Fin r × Fin r) A).mapMatrix l * (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) := by`. Apply `Matrix.ext` to reduce the goal to its premises.

Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `show rowAct A l (X (i, j)) = ∑ b, C (l i b) * X (b, j)`. Simplify using `[rowAct]`. Use `hA.trans ?_` and prove the remaining obligations.

Rewrite using `[hM, Matrix.det_mul, ← RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem detFactsP : DetFactsP := by
  intro A _ r e
  constructor
  · have h1 : detY A r ∈ dualWeyl A r r (qcOm r r) := by
      rw [← qc_full_minor A r r le_rfl id strictMono_id rfl]
      exact qc_initMinor_mem A id le_rfl
    have h2 := qc_pow_mem A r r _ _ h1 e
    have e1 : e • qcOm r r = fun _ => e := by
      funext t
      simp [qcOm, t.isLt]
    rwa [e1] at h2
  · intro l
    unfold detY
    have hA := AlgHom.map_det (rowAct A (n := r) l) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
    have hM : (rowAct A (n := r) l).mapMatrix (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) =
        (C : A →+* MvPolynomial (Fin r × Fin r) A).mapMatrix l *
          (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A)) := by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply]
      show rowAct A l (X (i, j)) = ∑ b, C (l i b) * X (b, j)
      simp [rowAct]
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, ← RingHom.map_det]
    rfl

/- English proof (translation)
Introduce `p a c r ell hp hr hl hc`. Unfold `N0 deF kappaOneExponent lgA`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `hN : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2`. Establish `h0 : r * (r - 1) / 2 ≤ (r + 1) ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `h0` after adjusting the coercions. Establish `h1 : Nat.log p (ell + r - 1) ≤ Nat.log p (8 * a + (r + 1))` using `Nat.log_mono_right (by omega)`. Establish `h2 : (Nat.log p (8 * a + (r + 1)) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ)` using `by first`. Consider the case `exact Real.natLog_le_logb _ _`.

Consider the case `(have hpow := Nat.pow_log_le_self p (x := 8 * a + (r + 1)) (by omega)`. Rewrite using `[Real.le_logb_iff_rpow_le hp1 (by positivity)]`. Conclude with `hpow)` after adjusting the coercions. Establish `h3 : (Nat.log p (ell + r - 1) : ℝ) ≤ Nat.log p (8 * a + (r + 1))` using `by exact_mod_cast h1`. Establish `hL : (Nat.log p (ell + r - 1) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) + 1` using `by linarith`.

Move the coercions through the operations in `at hL hN`. Establish `key : ((r * (r - 1) / 2 * Nat.log p (ell + r - 1) : ℕ) : ℝ) ≤ ((r : ℝ) + 1) ^ 2 * (Real.logb p (8 * (a : ℝ) + ((r : ℝ) + 1)) + 1)`. Use `push_cast`. Conclude with `mul_le_mul hN hL (Nat.cast_nonneg _) (by positivity)`. Establish `key2` using `key.trans (Nat.le_ceil _)`.

Move the coercions through the operations in `at key2 ⊢`. Conclude with `key2` after adjusting the coercions.
-/
theorem numP : NumP := by
  intro p a c r ell hp hr hl hc
  unfold N0 deF kappaOneExponent lgA
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hN : ((r * (r - 1) / 2 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
    have h0 : r * (r - 1) / 2 ≤ (r + 1) ^ 2 := by
      calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
        _ ≤ (r + 1) * (r + 1) := Nat.mul_le_mul (by omega) (by omega)
        _ = (r + 1) ^ 2 := by ring
    exact_mod_cast h0
  have h1 : Nat.log p (ell + r - 1) ≤ Nat.log p (8 * a + (r + 1)) := Nat.log_mono_right (by omega)
  have h2 : (Nat.log p (8 * a + (r + 1)) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) := by
    first
    | exact Real.natLog_le_logb _ _
    | (have hpow := Nat.pow_log_le_self p (x := 8 * a + (r + 1)) (by omega)
       rw [Real.le_logb_iff_rpow_le hp1 (by positivity)]
       exact_mod_cast hpow)
  have h3 : (Nat.log p (ell + r - 1) : ℝ) ≤ Nat.log p (8 * a + (r + 1)) := by exact_mod_cast h1
  have hL : (Nat.log p (ell + r - 1) : ℝ) ≤ Real.logb p ((8 * a + (r + 1) : ℕ) : ℝ) + 1 := by linarith
  push_cast at hL hN
  have key : ((r * (r - 1) / 2 * Nat.log p (ell + r - 1) : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) ^ 2 * (Real.logb p (8 * (a : ℝ) + ((r : ℝ) + 1)) + 1) := by
    push_cast
    exact mul_le_mul hN hL (Nat.cast_nonneg _) (by positivity)
  have key2 := key.trans (Nat.le_ceil _)
  push_cast at key2 ⊢
  exact_mod_cast key2

end Formalism.MainNotions.flipOneThree.Pf

end
