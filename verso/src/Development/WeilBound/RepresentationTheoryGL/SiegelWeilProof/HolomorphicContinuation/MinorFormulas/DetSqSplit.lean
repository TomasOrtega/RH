import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeH

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

/- English proof (translation)
Establish `hM : M0 * M0⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)`. Use `set N := M0⁻¹ * A with hN`. Use `set P : Polynomial ℂ := (det (1 + (Polynomial.X : Polynomial ℂ) • N.map Polynomial.C)).divX.divX with hP`. Establish `e : (fun t : ℂ => (M0 + t • A).det) = fun t : ℂ => M0.det * (1 + N.trace * t + P.eval t * t ^ 2)`. Use function extensionality and compare the values at `t`.

Establish `: M0 + t • A = M0 * (1 + t • N)`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, ← Matrix.mul_assoc, hM, Matrix.one_mul]`. Rewrite using `[this, Matrix.det_mul, Matrix.det_one_add_smul]`. Rewrite using `[e]`. Establish `h1 : HasDerivAt (fun t : ℂ => 1 + N.trace * t + P.eval t * t ^ 2) N.trace 0`.

Establish `ha : HasDerivAt (fun t : ℂ => N.trace * t) N.trace 0`. Simplify using `using (hasDerivAt_id (0 : ℂ)).const_mul N.trace`. Establish `hb : HasDerivAt (fun t : ℂ => P.eval t * t ^ 2) 0 0`. Use `(P.hasDerivAt (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ))` as an intermediate fact. Simplify using `using this`.

Simplify using `using (ha.const_add 1).fun_add hb`. Conclude with `h1.const_mul M0.det`.
-/
theorem det_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    HasDerivAt (fun t : ℂ => (M0 + t • A).det) (M0.det * (M0⁻¹ * A).trace) 0 := by
  have hM : M0 * M0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h)
  set N := M0⁻¹ * A with hN
  set P : Polynomial ℂ := (det (1 + (Polynomial.X : Polynomial ℂ) • N.map Polynomial.C)).divX.divX with hP
  have e : (fun t : ℂ => (M0 + t • A).det) = fun t : ℂ => M0.det * (1 + N.trace * t + P.eval t * t ^ 2) := by
    funext t
    have : M0 + t • A = M0 * (1 + t • N) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hN, ← Matrix.mul_assoc, hM, Matrix.one_mul]
    rw [this, Matrix.det_mul, Matrix.det_one_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℂ => 1 + N.trace * t + P.eval t * t ^ 2) N.trace 0 := by
    have ha : HasDerivAt (fun t : ℂ => N.trace * t) N.trace 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul N.trace
    have hb : HasDerivAt (fun t : ℂ => P.eval t * t ^ 2) 0 0 := by
      have := (P.hasDerivAt (0 : ℂ)).fun_mul (hasDerivAt_pow 2 (0 : ℂ))
      simpa using this
    simpa using (ha.const_add 1).fun_add hb
  exact h1.const_mul M0.det

/- English proof (translation)
Apply the tactic sequence `rcases hs with rfl | rfl <;> simp [Complex.I_mul_I]`.
-/
theorem c_sq (s : ℂ) (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rcases hs with rfl | rfl <;> simp [Complex.I_mul_I]

/- English proof (translation)
Rewrite using `[← Matrix.det_mul]`. Use `congr 1`. Establish `hc` using `c_sq s hs`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]`. Simplify using `only [neg_smul, one_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem det_sq_split (s : ℂ) (hs : s = 1 ∨ s = -1) (B : MC n) :
    (1 + Matrix.of B * Matrix.of B).det =
      (1 - (Complex.I * s) • Matrix.of B).det * (1 + (Complex.I * s) • Matrix.of B).det := by
  rw [← Matrix.det_mul]
  congr 1
  have hc := c_sq s hs
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
  simp only [neg_smul, one_smul]
  abel

/- English proof (translation)
Introduce `n s hs z m x v hx`. Take `⟨h1, h2, h3⟩` from `hx`. Use `set c : ℂ := Complex.I * s with hc`. Use `set M0 : Matrix (Fin n) (Fin n) ℂ := 1 - c • Matrix.of x`. Use `set M0' : Matrix (Fin n) (Fin n) ℂ := 1 + c • Matrix.of x`.

Use `set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of v`. Establish `hdM` using `det_line M0 (-c • V) h1`. Establish `hdM'` using `det_line M0' (c • V) h2`. Establish `e : (fun t : ℂ => clsC s z m 0 1 (x + t • v)) = fun t : ℂ => Complex.exp (-z * Complex.log ((M0 + t • (-c • V)).det * (M0' + t • (c • V)).det)) * (((M0 + t • (-c • V)).det)⁻¹) ^ m`. Use function extensionality and compare the values at `t`.

Simplify using `only [clsC, pow_zero, mul_one, map_one]`. Rewrite using `[det_sq_split s hs, mX, mY, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Rewrite using `[e]`. Establish `hW0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det ∈ Complex.slitPlane`. Establish `e0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det = (1 + Matrix.of x * Matrix.of x).det`.

Simplify using `only [zero_smul, add_zero]`. Conclude with `(det_sq_split s hs x).symm`. Rewrite using `[e0]`. Conclude with `h3`. Establish `hW` using `hdM.fun_mul hdM'`.

Establish `hL` using `hW.clog (by simpa using hW0)`. Establish `hE` using `(hL.const_mul (-z)).cexp`. Establish `hD` using `(hdM.inv (by simpa using h1)).pow m`. Establish `hT` using `hE.fun_mul hD`. Use `hT.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [zero_smul, add_zero]`. Establish `hM0 : M0.det ≠ 0` using `h1`. Establish `hM0' : M0'.det ≠ 0` using `h2`. Establish `tr1 : (M0⁻¹ * (-c • V)).trace = -c * (Ym s x * V).trace`. Rewrite using `[Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Establish `tr2 : (M0'⁻¹ * (c • V)).trace = c * (Yp s x * V).trace`. Rewrite using `[Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]`. Both sides reduce to the same expression. Establish `ecls : clsC s z m 0 1 x = Complex.exp (-z * Complex.log (M0.det * M0'.det)) * (M0.det⁻¹) ^ m`.

Simplify using `only [clsC, pow_zero, mul_one, map_one]`. Rewrite using `[det_sq_split s hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']`. Rewrite using `[ecls, tr1, tr2]`. Simplify using `only [Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero]`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]`.

Clear the denominators using the available nonvanishing facts. Establish `hinv : M0.det * M0.det⁻¹ = 1` using `mul_inv_cancel₀ hM0`. Take the linear combination `(-(c * (Ym s x * V).trace * M0.det⁻¹ ^ k) * (1 + (k : ℂ))) * hinv`.
-/
theorem hCls : HCls := by
  intro n s hs z m x v hx
  obtain ⟨h1, h2, h3⟩ := hx
  set c : ℂ := Complex.I * s with hc
  set M0 : Matrix (Fin n) (Fin n) ℂ := 1 - c • Matrix.of x
  set M0' : Matrix (Fin n) (Fin n) ℂ := 1 + c • Matrix.of x
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of v
  have hdM := det_line M0 (-c • V) h1
  have hdM' := det_line M0' (c • V) h2

  have e : (fun t : ℂ => clsC s z m 0 1 (x + t • v)) = fun t : ℂ =>
      Complex.exp (-z * Complex.log ((M0 + t • (-c • V)).det * (M0' + t • (c • V)).det)) * (((M0 + t • (-c • V)).det)⁻¹) ^ m := by
    funext t
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, mX, mY, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e]
  have hW0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det ∈ Complex.slitPlane := by
    have e0 : (M0 + (0 : ℂ) • (-c • V)).det * (M0' + (0 : ℂ) • (c • V)).det = (1 + Matrix.of x * Matrix.of x).det := by
      simp only [zero_smul, add_zero]
      exact (det_sq_split s hs x).symm
    rw [e0]
    exact h3
  have hW := hdM.fun_mul hdM'
  have hL := hW.clog (by simpa using hW0)
  have hE := (hL.const_mul (-z)).cexp
  have hD := (hdM.inv (by simpa using h1)).pow m
  have hT := hE.fun_mul hD
  refine hT.congr_deriv ?_
  simp only [zero_smul, add_zero]
  have hM0 : M0.det ≠ 0 := h1
  have hM0' : M0'.det ≠ 0 := h2
  have tr1 : (M0⁻¹ * (-c • V)).trace = -c * (Ym s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have tr2 : (M0'⁻¹ * (c • V)).trace = c * (Yp s x * V).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rfl
  have ecls : clsC s z m 0 1 x = Complex.exp (-z * Complex.log (M0.det * M0'.det)) * (M0.det⁻¹) ^ m := by
    simp only [clsC, pow_zero, mul_one, map_one]
    rw [det_sq_split s hs, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [ecls, tr1, tr2]
  simp only [Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    have hinv : M0.det * M0.det⁻¹ = 1 := mul_inv_cancel₀ hM0
    linear_combination (-(c * (Ym s x * V).trace * M0.det⁻¹ ^ k) * (1 + (k : ℂ))) * hinv

end PositivityTheory.Rg.Sw.SP
