import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens.ThetaFrame

open ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

/- English proof (translation)
Establish `hU : ∀ a c : Fin m, c < a → Tᴴᵀ a c = 0` using `fun a c hac => by`. Simplify using `[Matrix.transpose_apply, Matrix.conjTranspose_apply, hT a c hac]`. Establish `h1` using `sub_LMU hk T M Tᴴᵀ hT hU`. Establish `h2` using `sub_LMU hk T N Tᴴᵀ hT hU`. Rewrite `h1` using `[show Tᵀ * M * Tᴴᵀ = chg T M from rfl, h, Matrix.submatrix_one _ (Fin.castLE_injective hk)]`.

Rewrite `h2` using `[show Tᵀ * N * Tᴴᵀ = chg T N from rfl]`. Rewrite using `[h2]`. Use `set P := (T.submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ`. Use `set Q := Tᴴᵀ.submatrix (Fin.castLE hk) (Fin.castLE hk)`. Use `set A := M.submatrix (Fin.castLE hk) (Fin.castLE hk)`.

Establish `e1 : P * (A * Q) = 1` using `by rw [← Matrix.mul_assoc]; exact h1.symm`. Establish `e2 : A * (Q * P) = 1`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `mul_eq_one_comm.1 e1`. Rewrite using `[Matrix.inv_eq_right_inv e2, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]`.
-/
theorem trace_sub_inv_mul {m k : ℕ} (hk : k ≤ m) (M N T : Matrix (Fin m) (Fin m) ℂ)
    (hT : ∀ a c : Fin m, c < a → T a c = 0) (h : chg T M = 1) :
    ((M.submatrix (Fin.castLE hk) (Fin.castLE hk))⁻¹ * N.submatrix (Fin.castLE hk) (Fin.castLE hk)).trace =
      ((chg T N).submatrix (Fin.castLE hk) (Fin.castLE hk)).trace := by
  have hU : ∀ a c : Fin m, c < a → Tᴴᵀ a c = 0 := fun a c hac => by
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply, hT a c hac]
  have h1 := sub_LMU hk T M Tᴴᵀ hT hU
  have h2 := sub_LMU hk T N Tᴴᵀ hT hU
  rw [show Tᵀ * M * Tᴴᵀ = chg T M from rfl, h, Matrix.submatrix_one _ (Fin.castLE_injective hk)] at h1
  rw [show Tᵀ * N * Tᴴᵀ = chg T N from rfl] at h2
  rw [h2]
  set P := (T.submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ
  set Q := Tᴴᵀ.submatrix (Fin.castLE hk) (Fin.castLE hk)
  set A := M.submatrix (Fin.castLE hk) (Fin.castLE hk)
  have e1 : P * (A * Q) = 1 := by rw [← Matrix.mul_assoc]; exact h1.symm
  have e2 : A * (Q * P) = 1 := by
    rw [← Matrix.mul_assoc]; exact mul_eq_one_comm.1 e1
  rw [Matrix.inv_eq_right_inv e2, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[sum_eq_castLE hk]`. Simplify using `[Matrix.trace]`. Introduce `c hc`. Simplify using `[not_lt.2 hc]`.
-/
theorem trace_sub_eq_sum {m k : ℕ} (hk : k ≤ m) (A : Matrix (Fin m) (Fin m) ℂ) :
    (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).trace = ∑ c : Fin m, if (c : ℕ) < k then A c c else 0 := by
  rw [sum_eq_castLE hk]
  · simp [Matrix.trace]
  · intro c hc
    simp [not_lt.2 hc]

/- English proof (translation)
Establish `e : Bᵀ * (G * Bᴴᵀ) = 1` using `by rw [← Matrix.mul_assoc]; exact h`. Establish `hinv : (Bᵀ)⁻¹ = G * Bᴴᵀ` using `Matrix.inv_eq_right_inv e`. Simplify using `only [chg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hinv, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.
-/
theorem chg_neg_mul {m : ℕ} (G F B : Matrix (Fin m) (Fin m) ℂ) (h : chg B G = 1) :
    chg B (-(Fᵀ * G)) = -(B⁻¹ * F * B)ᵀ := by
  have e : Bᵀ * (G * Bᴴᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact h
  have hinv : (Bᵀ)⁻¹ = G * Bᴴᵀ := Matrix.inv_eq_right_inv e
  simp only [chg, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hinv, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]

/- English proof (translation)
Unfold `logMinorDer`. Rewrite using `[trace_sub_inv_mul _ _ _ T hT h, chg_chg, chg_neg_mul G F (uni n * T) (by rw [← chg_chg]; exact h), trace_sub_eq_sum]`. Simplify using `only [Matrix.neg_apply, Matrix.transpose_apply]`.
-/
theorem logMinorDer_eq {m : ℕ} (G F : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ) (T : Matrix (Fin m) (Fin m) ℂ)
    (hT : ∀ a c : Fin m, c < a → T a c = 0) (h : chg T (chg (uni n) G) = 1) (j : Fin (m + 1)) :
    logMinorDer G (-(Fᵀ * G)) n j =
      (∑ c : Fin m, if (c : ℕ) < j then -(((uni n * T)⁻¹ * F * (uni n * T)) c c) else 0).re := by
  unfold logMinorDer
  rw [trace_sub_inv_mul _ _ _ T hT h, chg_chg, chg_neg_mul G F (uni n * T) (by rw [← chg_chg]; exact h),
    trace_sub_eq_sum]
  simp only [Matrix.neg_apply, Matrix.transpose_apply]

end GlobalTheory.MixDens.ThetaFrame

open GlobalTheory.MixDens.ThetaFrame in

/- English proof (translation)
Introduce `m G F n T hT h i`. Unfold `theta`. Rewrite using `[logMinorDer_eq G F n T hT h, logMinorDer_eq G F n T hT h, ← Complex.sub_re, ← Finset.sum_sub_distrib]`. Use `congr 1`. Rewrite using `[show ((uni n * T)⁻¹ * F * (uni n * T)) i i = ∑ c : Fin m, if c = i then ((uni n * T)⁻¹ * F * (uni n * T)) c c else 0 by simp]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.coe_castSucc, Fin.val_succ]`. Distinguish the cases in `hci : c = i`. Substitute `hci` using the available equality. Simplify using the standard rewrite rules.

Establish `: (c : ℕ) ≠ i` using `fun e => hci (Fin.ext e)`. Distinguish the cases in `hc : (c : ℕ) < i`. Rewrite using `[if_pos hc, if_pos (by omega), if_neg hci]; ring`. Rewrite using `[if_neg hc, if_neg (by omega), if_neg hci]; ring`.
-/
theorem GlobalTheory.MixDens.theta_eq_re_diag : ∀ {m : ℕ} (G F : Matrix (Fin m) (Fin m) ℂ) (n : Low m → ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ), (∀ a c : Fin m, c < a → T a c = 0) → chg T (chg (uni n) G) = 1 →
    ∀ i : Fin m, theta G (-(Fᵀ * G)) n i = (((uni n * T)⁻¹ * F * (uni n * T)) i i).re := by
  intro m G F n T hT h i
  unfold theta
  rw [logMinorDer_eq G F n T hT h, logMinorDer_eq G F n T hT h, ← Complex.sub_re, ← Finset.sum_sub_distrib]
  congr 1
  rw [show ((uni n * T)⁻¹ * F * (uni n * T)) i i =
      ∑ c : Fin m, if c = i then ((uni n * T)⁻¹ * F * (uni n * T)) c c else 0 by simp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.coe_castSucc, Fin.val_succ]
  by_cases hci : c = i
  · subst hci; simp
  · have : (c : ℕ) ≠ i := fun e => hci (Fin.ext e)
    by_cases hc : (c : ℕ) < i
    · rw [if_pos hc, if_pos (by omega), if_neg hci]; ring
    · rw [if_neg hc, if_neg (by omega), if_neg hci]; ring
