import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnipotentExpHaarSqrtBound

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [S7.hs, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `norm_cast`.
-/
theorem hs_eq_re_trace (A : Matrix (Fin n) (Fin n) ℂ) :
    S7.hs A = (trace (Aᴴ * A)).re := by
  simp only [S7.hs, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

/- English proof (translation)
Set `_ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.frobeniusNormedAddCommGroup`. Establish `key : ∀ M : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (S7.hs M) = ‖M‖`. Introduce `M`. Rewrite using `[Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, S7.hs]`. Evaluate the numerical expressions.

Rewrite using `[key, key, key]`. Conclude with `Matrix.frobenius_norm_mul A B`.
-/
theorem sqrt_hs_mul (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (S7.hs (A * B)) ≤ Real.sqrt (S7.hs A) * Real.sqrt (S7.hs B) := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (S7.hs M) = ‖M‖ := by
    intro M
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, S7.hs]
    norm_num
  rw [key, key, key]
  exact Matrix.frobenius_norm_mul A B

/- English proof (translation)
Rewrite using `[trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]`.
-/
theorem trace_conj {V W A : Matrix (Fin n) (Fin n) ℂ} (h : W * V = 1) :
    trace (V * A * W) = trace A := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]

/- English proof (translation)
Establish `key : ∀ y : ℝ, 0 ≤ y → Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 ≤ 4 * y ^ 2 * Real.exp (2 * y)`. Introduce `y hy`. Establish `e1 : Real.exp (2 * y) = Real.exp y * Real.exp y` using `by rw [← Real.exp_add]; ring_nf`. Establish `e2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y)`. Rewrite using `[← Real.exp_add]`.

Put the polynomial expressions in normal form. Establish `e3 : Real.exp y * Real.exp (-y) = 1` using `by rw [← Real.exp_add]; simp`. Establish `h1` using `Real.add_one_le_exp (-(2 * y))`. Establish `hpos` using `Real.exp_pos y`. Establish `hu0 : 0 ≤ Real.exp y - Real.exp (-y)`.

Use `Real.exp_le_exp.mpr (show -y ≤ y by linarith); linarith` as an intermediate fact. Establish `h2` using `mul_le_mul_of_nonneg_left h1 hpos.le`. Rewrite `h2` using `[e2]`. Establish `h3 : Real.exp y * (Real.exp (-y) * Real.exp (-y)) = Real.exp (-y)`. Rewrite using `[← mul_assoc, e3, one_mul]`.

Establish `hu : Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp y` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2]`. Use polynomial arithmetic with `[e3]`. Use `_ ≤ (2 * y * Real.exp y) ^ 2 := pow_le_pow_left₀ hu0 hu 2`.

Use `_ = 4 * y ^ 2 * Real.exp (2 * y) := by rw [e1]; ring`. Break down `le_total 0 x with hx | hx` into its components or cases. Rewrite using `[abs_of_nonneg hx]`. Conclude with `key x hx`. Use `key (-x) (by linarith)` as an intermediate fact.

Rewrite using `[abs_of_nonpos hx]`. Establish `e : -(2 * -x) = 2 * x` using `by ring`. Rewrite `this` using `[e]`. Establish `e' : (-x) ^ 2 = x ^ 2` using `by ring`. Rewrite `this` using `[e']`.

Rewrite `this`, the goal using `[show 2 * -x = -(2 * x) by ring]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem phi_le (x : ℝ) :
    Real.exp (2 * x) + Real.exp (-(2 * x)) - 2 ≤ 4 * x ^ 2 * Real.exp (2 * |x|) := by
  have key : ∀ y : ℝ, 0 ≤ y →
      Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 ≤ 4 * y ^ 2 * Real.exp (2 * y) := by
    intro y hy
    have e1 : Real.exp (2 * y) = Real.exp y * Real.exp y := by rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have h1 := Real.add_one_le_exp (-(2 * y))
    have hpos := Real.exp_pos y
    have hu0 : 0 ≤ Real.exp y - Real.exp (-y) := by
      have := Real.exp_le_exp.mpr (show -y ≤ y by linarith); linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [e2] at h2
    have h3 : Real.exp y * (Real.exp (-y) * Real.exp (-y)) = Real.exp (-y) := by
      rw [← mul_assoc, e3, one_mul]
    have hu : Real.exp y - Real.exp (-y) ≤ 2 * y * Real.exp y := by nlinarith
    calc Real.exp (2 * y) + Real.exp (-(2 * y)) - 2 = (Real.exp y - Real.exp (-y)) ^ 2 := by
          rw [e1, e2]; nlinarith [e3]
      _ ≤ (2 * y * Real.exp y) ^ 2 := pow_le_pow_left₀ hu0 hu 2
      _ = 4 * y ^ 2 * Real.exp (2 * y) := by rw [e1]; ring
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact key x hx
  · have := key (-x) (by linarith)
    rw [abs_of_nonpos hx]
    have e : -(2 * -x) = 2 * x := by ring
    rw [e] at this
    have e' : (-x) ^ 2 = x ^ 2 := by ring
    rw [e'] at this
    rw [show 2 * -x = -(2 * x) by ring] at this ⊢
    linarith

/- English proof (translation)
Establish `h : Real.exp 2 = Real.exp 1 * Real.exp 1` using `by rw [← Real.exp_add]; norm_num`. Establish `h1` using `Real.exp_one_lt_d9`. Establish `h2` using `Real.exp_pos 1`. Rewrite using `[h]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_two_lt : Real.exp 2 < 7.5 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos 1
  rw [h]; nlinarith

/- English proof (translation)
Use `set A1 : ℝ := D ^ 2 * 49 ^ m * 30 with hA1d`. Use `set B : ℝ := D ^ 2 * 9 ^ (m + 1) with hBd`. Establish `hB : 0 ≤ B` using `by positivity`. Use `set A2 : ℝ := Real.log (1 + B) + 4 * ((m : ℝ) + 1) with hA2d`. Establish `hA1 : 0 ≤ A1` using `by positivity`.

Establish `hlB : 0 ≤ Real.log (1 + B)` using `Real.log_nonneg (by linarith)`. Establish `hA2 : 0 ≤ A2` using `by positivity`. Use `⟨max A1 A2, le_max_of_le_left hA1, fun s a y hs ha hy haS hyA => ?_⟩` and prove the remaining obligations. Establish `hσ0 : 0 ≤ Real.sqrt s` using `Real.sqrt_nonneg s`. Establish `hσs : Real.sqrt s ^ 2 = s` using `Real.sq_sqrt hs`.

Establish `hsa0 : 0 ≤ Real.sqrt a` using `Real.sqrt_nonneg a`. Establish `hsa : Real.sqrt a ^ 2 = a` using `Real.sq_sqrt ha`. Establish `hlog : Real.log (1 + y) ≤ y`. Use `Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith` as an intermediate fact. Establish `hD2 : 0 ≤ D ^ 2` using `sq_nonneg D`.

Break down `le_total s 1 with h1 | h1` into its components or cases. Establish `hσ1 : Real.sqrt s ≤ 1`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]`. Conclude with `Real.sqrt_le_sqrt h1`. Establish `hmin : min s (Real.sqrt s) = s` using `min_eq_left (by nlinarith)`.

Establish `he : Real.exp (2 * Real.sqrt s) ≤ 7.5` using `(Real.exp_le_exp.mpr (by linarith)).trans exp_two_lt.le`. Establish `ha30 : a ≤ 30 * s` using `by nlinarith`. Establish `ha36 : a ≤ 36` using `by linarith`. Establish `hsq6 : Real.sqrt a ≤ 6`. Use `Real.sqrt_le_sqrt ha36` as an intermediate fact.

Rewrite `this` using `[show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]`. Then use the resulting hypothesis. Establish `hp : (1 + Real.sqrt a) ^ (2 * m) ≤ 49 ^ m`. Combine the equalities or inequalities in the displayed calculation. Establish `hy2 : y ≤ A1 * s`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul (mul_le_mul_of_nonneg_left ha30 hD2) hp (by positivity) (by positivity)` to reduce the goal to its premises. Use `_ = A1 * s := by rw [hA1d]; ring`. Rewrite using `[hmin]`. Combine the equalities or inequalities in the displayed calculation. Establish `hσ1 : 1 ≤ Real.sqrt s`.

Rewrite using `[show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]`. Conclude with `Real.sqrt_le_sqrt h1`. Establish `hmin : min s (Real.sqrt s) = Real.sqrt s` using `min_eq_right (by nlinarith)`. Use `set σ := Real.sqrt s with hσ`. Use `set E := Real.exp σ with hE`.

Establish `hE1 : 1 ≤ E` using `Real.one_le_exp hσ0`. Establish `hσE : σ ≤ E` using `by have := Real.add_one_le_exp σ; linarith`. Establish `he2 : Real.exp (2 * σ) = E * E` using `by rw [hE, ← Real.exp_add]; ring_nf`. Establish `hsa1 : Real.sqrt a ≤ 2 * σ * E`. Establish `h2 : a ≤ (2 * σ * E) ^ 2` using `by rw [← hσs] at haS; rw [he2] at haS; nlinarith`.

Use `Real.sqrt_le_sqrt h2` as an intermediate fact. Rewrite `this` using `[Real.sqrt_sq (by positivity)]`. Then use the resulting hypothesis. Establish `hsa2 : 1 + Real.sqrt a ≤ 3 * E ^ 2` using `by nlinarith`. Establish `hy2 : y ≤ B * Real.exp (4 * ((m : ℝ) + 1) * σ)`. Establish `hexp : Real.exp (4 * ((m : ℝ) + 1) * σ) = E ^ (4 * (m + 1))`.

Rewrite using `[hE, ← Real.exp_nat_mul]`. Use `push_cast`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hexp, hBd, mul_pow, ← pow_mul, pow_mul 3 2 (m + 1)]`.

Put the polynomial expressions in normal form. Establish `hX1 : 1 ≤ Real.exp (4 * ((m : ℝ) + 1) * σ)` using `Real.one_le_exp (by positivity)`. Establish `h3 : 1 + y ≤ (1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ)` using `by nlinarith`. Establish `h4 : Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_bound (D : ℝ) (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ s a y : ℝ, 0 ≤ s → 0 ≤ a → 0 ≤ y →
    a ≤ 4 * s * Real.exp (2 * Real.sqrt s) → y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) →
    Real.log (1 + y) ≤ A * min s (Real.sqrt s) := by
  set A1 : ℝ := D ^ 2 * 49 ^ m * 30 with hA1d
  set B : ℝ := D ^ 2 * 9 ^ (m + 1) with hBd
  have hB : 0 ≤ B := by positivity
  set A2 : ℝ := Real.log (1 + B) + 4 * ((m : ℝ) + 1) with hA2d
  have hA1 : 0 ≤ A1 := by positivity
  have hlB : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  have hA2 : 0 ≤ A2 := by positivity
  refine ⟨max A1 A2, le_max_of_le_left hA1, fun s a y hs ha hy haS hyA => ?_⟩
  have hσ0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hσs : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hlog : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith); linarith
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  rcases le_total s 1 with h1 | h1
  · have hσ1 : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = s := min_eq_left (by nlinarith)
    have he : Real.exp (2 * Real.sqrt s) ≤ 7.5 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_two_lt.le
    have ha30 : a ≤ 30 * s := by nlinarith
    have ha36 : a ≤ 36 := by linarith
    have hsq6 : Real.sqrt a ≤ 6 := by
      have := Real.sqrt_le_sqrt ha36
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have hp : (1 + Real.sqrt a) ^ (2 * m) ≤ 49 ^ m := by
      calc (1 + Real.sqrt a) ^ (2 * m) ≤ 7 ^ (2 * m) :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 49 ^ m := by rw [pow_mul]; norm_num
    have hy2 : y ≤ A1 * s := by
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (30 * s) * 49 ^ m := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left ha30 hD2) hp (by positivity) (by positivity)
        _ = A1 * s := by rw [hA1d]; ring
    rw [hmin]
    calc Real.log (1 + y) ≤ A1 * s := hlog.trans hy2
      _ ≤ max A1 A2 * s := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  · have hσ1 : 1 ≤ Real.sqrt s := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
    have hmin : min s (Real.sqrt s) = Real.sqrt s := min_eq_right (by nlinarith)
    set σ := Real.sqrt s with hσ
    set E := Real.exp σ with hE
    have hE1 : 1 ≤ E := Real.one_le_exp hσ0
    have hσE : σ ≤ E := by have := Real.add_one_le_exp σ; linarith
    have he2 : Real.exp (2 * σ) = E * E := by rw [hE, ← Real.exp_add]; ring_nf
    have hsa1 : Real.sqrt a ≤ 2 * σ * E := by
      have h2 : a ≤ (2 * σ * E) ^ 2 := by rw [← hσs] at haS; rw [he2] at haS; nlinarith
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (by positivity)] at this
    have hsa2 : 1 + Real.sqrt a ≤ 3 * E ^ 2 := by nlinarith
    have hy2 : y ≤ B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
      have hexp : Real.exp (4 * ((m : ℝ) + 1) * σ) = E ^ (4 * (m + 1)) := by
        rw [hE, ← Real.exp_nat_mul]; push_cast; ring_nf
      calc y ≤ D ^ 2 * a * (1 + Real.sqrt a) ^ (2 * m) := hyA
        _ ≤ D ^ 2 * (1 + Real.sqrt a) ^ 2 * (1 + Real.sqrt a) ^ (2 * m) := by
            gcongr; nlinarith
        _ = D ^ 2 * (1 + Real.sqrt a) ^ (2 * (m + 1)) := by ring
        _ ≤ D ^ 2 * (3 * E ^ 2) ^ (2 * (m + 1)) := by gcongr
        _ = B * Real.exp (4 * ((m : ℝ) + 1) * σ) := by
            rw [hexp, hBd, mul_pow, ← pow_mul, pow_mul 3 2 (m + 1)]; ring_nf
    have hX1 : 1 ≤ Real.exp (4 * ((m : ℝ) + 1) * σ) := Real.one_le_exp (by positivity)
    have h3 : 1 + y ≤ (1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ) := by nlinarith
    have h4 : Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := by
      calc Real.log (1 + y) ≤ Real.log ((1 + B) * Real.exp (4 * ((m : ℝ) + 1) * σ)) :=
            Real.log_le_log (by linarith) h3
        _ = _ := by rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    rw [hmin]
    calc Real.log (1 + y) ≤ Real.log (1 + B) + 4 * ((m : ℝ) + 1) * σ := h4
      _ ≤ A2 * σ := by rw [hA2d]; nlinarith
      _ ≤ max A1 A2 * σ := mul_le_mul_of_nonneg_right (le_max_right _ _) hσ0

/- English proof (translation)
Establish `h1` using `Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2`. Establish `h2` using `Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2`. Use `⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]`. Both sides reduce to the same expression.

Use `conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]`. Establish `hinv : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹` using `(Matrix.inv_eq_left_inv h1).symm`. Establish `hu : IsUnit (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)` using `⟨⟨_, _, h2, h1⟩, rfl⟩`. Rewrite using `[hinv, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal]`. Use `congr 3`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.coe_exp]`. Simplify using `[← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]`.
-/
theorem herm_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsHermitian) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), star V * V = 1 ∧ V * star V = 1 ∧
      X = V * diagonal (fun i => (l i : ℂ)) * star V ∧
      NormedSpace.exp X = V * diagonal (fun i => (Real.exp (l i) : ℂ)) * star V := by
  have h1 := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have h2 := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  refine ⟨hX.eigenvectorUnitary, hX.eigenvalues, h1, h2, ?_, ?_⟩
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  · conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have hinv : star (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ :=
      (Matrix.inv_eq_left_inv h1).symm
    have hu : IsUnit (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
      ⟨⟨_, _, h2, h1⟩, rfl⟩
    rw [hinv, Matrix.exp_conj _ _ hu, Matrix.exp_diagonal]
    congr 3
    funext i
    rw [Pi.coe_exp]
    simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

/- English proof (translation)
Rewrite using `[hs_eq_re_trace]`. Simplify using `only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, ht, Complex.sub_re]`. Simplify using the standard rewrite rules.
-/
theorem hs_sub_one (g : Matrix (Fin n) (Fin n) ℂ) (ht : trace g = (n : ℂ)) :
    S7.hs (g - 1) = (trace (gᴴ * g)).re - n := by
  rw [hs_eq_re_trace]
  simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, ht, Complex.sub_re]
  simp

open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N in
open scoped Matrix.Norms.Operator in
/- English proof (translation)
Rewrite `hY` using `[lieOf_Nset_eq]`. Establish `h0` using `(mem_lieN.mp hY).1`. Establish `h1 : NormedSpace.exp Y - 1 ∈ levF (levB k r) 0` using `(isFilB (k := k) (r := r)).exp_shear.1 Y h0`. Establish `hnil : IsNilpotent (NormedSpace.exp Y - 1)`. Use `⟨2 * r + 1, ?_⟩` and prove the remaining obligations.

Use `(isFilB (k := k) (r := r)).pow_mem h1 (2 * r)` as an intermediate fact. Rewrite `this` using `[(isFilB (k := k) (r := r)).bot]`. Conclude with `(Submodule.mem_bot ℝ).mp this`. Establish `ht` using `(Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero`. Establish `e : NormedSpace.exp Y = 1 + (NormedSpace.exp Y - 1)` using `by abel`.

Rewrite using `[e, trace_add, ht, trace_one]`. Simplify using the standard rewrite rules.
-/
theorem trace_exp_lie {k r : ℕ} {Y : Mat k r} (hY : Y ∈ Formalism.MainNotions.S.lieOf (Formalism.QuantumDeterminants.Nset k r)) :
    trace (NormedSpace.exp Y) = ((2 * r + k + 1 : ℕ) : ℂ) := by
  rw [lieOf_Nset_eq] at hY
  have h0 := (mem_lieN.mp hY).1
  have h1 : NormedSpace.exp Y - 1 ∈ levF (levB k r) 0 := (isFilB (k := k) (r := r)).exp_shear.1 Y h0
  have hnil : IsNilpotent (NormedSpace.exp Y - 1) := by
    refine ⟨2 * r + 1, ?_⟩
    have := (isFilB (k := k) (r := r)).pow_mem h1 (2 * r)
    rw [(isFilB (k := k) (r := r)).bot] at this
    exact (Submodule.mem_bot ℝ).mp this
  have ht := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have e : NormedSpace.exp Y = 1 + (NormedSpace.exp Y - 1) := by abel
  rw [e, trace_add, ht, trace_one]
  simp

/- English proof (translation)
Take `⟨hG, hP⟩` from `h`. Establish `h1 : Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε = X * ReciprocityTheory.ChartRestriction.DS.Jm ε`. Rewrite using `[hP]`. Conclude with `eq_neg_of_add_eq_zero_left hG`. Establish `hJ` using `S7.Jm_mul_self ε`.

Use `show Xᴴ = X`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, hJ, Matrix.mul_one]`. Use `_ = X * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [h1]`. Use `_ = X := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]`.
-/
theorem herm_of_inP {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) : X.IsHermitian := by
  obtain ⟨hG, hP⟩ := h
  have h1 : Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε = X * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
    rw [hP]; exact eq_neg_of_add_eq_zero_left hG
  have hJ := S7.Jm_mul_self ε
  show Xᴴ = X
  calc Xᴴ = Xᴴ * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by
        rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = X * ReciprocityTheory.ChartRestriction.DS.Jm ε * ReciprocityTheory.ChartRestriction.DS.Jm ε := by rw [h1]
    _ = X := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

/- English proof (translation)
Establish `hP` using `h.2`. Establish `hc : ∃ b : Bool, ∀ a, ε a = b`. Break down `Nat.min_eq_zero_iff.mp hq with hp | hp` into its components or cases. Use `⟨false, fun a => ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[ReciprocityTheory.ChartRestriction.DS.pOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`.

Simplify using `using hp (Finset.mem_univ a)`. Use `⟨true, fun a => ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[ReciprocityTheory.ChartRestriction.DS.qOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Simplify using `using hp (Finset.mem_univ a)`. Take `⟨b, hb⟩` from `hc`.

Use extensionality with `i j`. Use `congrFun (congrFun hP i) j` as an intermediate fact. Simplify using `only [ReciprocityTheory.ChartRestriction.DS.Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hb] at this`. Apply the tactic sequence `cases b <;> simp at this`. Use `show X i j = 0`.

Take the linear combination `-this / 2`. Use `show X i j = 0`. Take the linear combination `this / 2`.
-/
theorem eq_zero_of_noncompactPart_of_noncompactRank_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : ReciprocityTheory.ChartRestriction.DS.inP ε X) (hq : S7.q0 ε = 0) : X = 0 := by
  have hP := h.2
  have hc : ∃ b : Bool, ∀ a, ε a = b := by
    rcases Nat.min_eq_zero_iff.mp hq with hp | hp
    · refine ⟨false, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.pOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
    · refine ⟨true, fun a => ?_⟩
      rw [ReciprocityTheory.ChartRestriction.DS.qOf, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hp
      simpa using hp (Finset.mem_univ a)
  obtain ⟨b, hb⟩ := hc
  ext i j
  have := congrFun (congrFun hP i) j
  simp only [ReciprocityTheory.ChartRestriction.DS.Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, hb] at this
  cases b <;> simp at this
  · show X i j = 0
    linear_combination -this / 2
  · show X i j = 0
    linear_combination this / 2

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.LieExponentialMajorant
