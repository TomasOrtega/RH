import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.LogCompress

/- English proof (translation)
Use `set m := ∑ j, w j * Real.exp (d j) with hm`. Establish `hpos : 0 < m`. Take `⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0` from `Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)`. Conclude with `Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le) ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩`. Establish `hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m`.

Introduce `j`. Rewrite using `[Real.exp_sub, Real.exp_log hpos]`. Establish `hnn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))` using `fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))`. Establish `hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) = Real.log m - ∑ j, w j * d j`. Establish `: ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1)`.

Introduce `j`. Rewrite using `[hexp]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨hpos, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.sum_nonneg hnn` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h j hj`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j (Finset.mem_univ _)`.

Establish `h2` using `(mul_eq_zero.1 h0).resolve_left hj`. Establish `h3 : d j - Real.log m = 0`. Assume the negation of the conclusion as `hne`. Use `Real.add_one_lt_exp hne` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : d j = Real.log m` using `by linarith`. Rewrite using `[h4, Real.exp_log hpos]`.
-/
theorem jensen_exp {ι : Type} [Fintype ι] (w d : ι → ℝ) (hw : ∀ j, 0 ≤ w j) (h1 : ∑ j, w j = 1) :
    0 < ∑ j, w j * Real.exp (d j) ∧ ∑ j, w j * d j ≤ Real.log (∑ j, w j * Real.exp (d j)) ∧
      (∑ j, w j * d j = Real.log (∑ j, w j * Real.exp (d j)) →
        ∀ j, w j ≠ 0 → Real.exp (d j) = ∑ j, w j * Real.exp (d j)) := by
  set m := ∑ j, w j * Real.exp (d j) with hm
  have hpos : 0 < m := by
    obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), w j ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [h1]; exact one_ne_zero)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
      ⟨j, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw j) hj.symm) (Real.exp_pos _)⟩
  have hexp : ∀ j, Real.exp (d j - Real.log m) = Real.exp (d j) / m := by
    intro j
    rw [Real.exp_sub, Real.exp_log hpos]
  have hnn : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1)) :=
    fun j _ => mul_nonneg (hw j) (sub_nonneg.2 (Real.add_one_le_exp _))
  have hsum : ∑ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
      = Real.log m - ∑ j, w j * d j := by
    have : ∀ j, w j * (Real.exp (d j - Real.log m) - (d j - Real.log m + 1))
        = w j * Real.exp (d j) / m - w j * d j + w j * (Real.log m - 1) := by
      intro j
      rw [hexp]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, h1, ← hm, div_self hpos.ne']
    ring
  refine ⟨hpos, ?_, ?_⟩
  · have := Finset.sum_nonneg hnn
    linarith
  · intro h j hj
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [hsum, h, sub_self]) j
      (Finset.mem_univ _)
    have h2 := (mul_eq_zero.1 h0).resolve_left hj
    have h3 : d j - Real.log m = 0 := by
      by_contra hne
      have := Real.add_one_lt_exp hne
      linarith
    have h4 : d j = Real.log m := by linarith
    rw [h4, Real.exp_log hpos]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem compress_diag {ι κ : Type} [Fintype ι] [DecidableEq ι] (C : Matrix ι κ ℂ) (f : ι → ℝ) (k : κ) :
    (Cᴴ * diagonal (fun i => (f i : ℂ)) * C) k k = ((∑ j, Complex.normSq (C j k) * f j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

/- English proof (translation)
Use `⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)`. Conclude with `(Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)`. Use `hB.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Simplify `this` using `[Matrix.star_eq_conjTranspose]`.
-/
theorem exists_diag {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (hB : B.IsHermitian) :
    ∃ (V : Matrix κ κ ℂ) (m : κ → ℂ), V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ Vᴴ * B * V = diagonal m := by
  refine ⟨hB.eigenvectorUnitary, RCLike.ofReal ∘ hB.eigenvalues, ?_, ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff.1 hB.eigenvectorUnitary.2)
  · exact (Matrix.mem_unitaryGroup_iff'.1 hB.eigenvectorUnitary.2)
  · have := hB.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this

/- English proof (translation)
Introduce `ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ`. Establish `hAh : A.IsHermitian`. Rewrite using `[hA]`. Use `Matrix.isHermitian_mul_mul_conjTranspose _ ?_` and prove the remaining obligations. Rewrite using `[Matrix.isHermitian_diagonal_iff]`.

Introduce `i`. Conclude with `Complex.conj_ofReal _`. Take `⟨V, m, hV, hV', hm⟩` from `exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)`. Use `set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC`. Establish `hCH : Cᴴ = Vᴴ * Qᴴ * U`.

Simplify using `[hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V`. Introduce `D`. Rewrite using `[hCH, hC]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1`. Introduce `k`. Establish `h` using `compress_diag C (fun _ => 1) k`. Establish `h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1` using `by simp`. Rewrite `h` using `[key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV']`.

Simplify using `only [Matrix.one_apply_eq, mul_one] at h`. Conclude with `h.symm` after adjusting the coercions. Establish `hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ)`. Introduce `k`. Rewrite using `[← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]`.

Establish `hJ` using `fun k => jensen_exp (fun j => Complex.normSq (C j k)) d (fun j => Complex.normSq_nonneg _) (hw k)`. Establish `hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j)`. Establish `h` using `congrArg Matrix.det hm`. Rewrite `h` using `[Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal]`. Rewrite using `[h]`.

Simplify using `only [hmk]`. Rewrite using `[← Complex.ofReal_prod, Complex.ofReal_re]`. Establish `htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j`. Establish `h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q)`. Rewrite using `[key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]`.

Rewrite using `[← h, Matrix.trace]`. Simplify using `only [Matrix.diag_apply, compress_diag]`. Rewrite using `[← Complex.ofReal_sum, Complex.ofReal_re]`. Rewrite using `[hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]`. Use `⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩` and prove the remaining obligations.

Establish `heq` using `(Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h`. Establish `hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m`. Use extensionality with `j k`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `h0 : C j k = 0`.

Simplify using `[h0]`. Use `(hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)` as an intermediate fact. Rewrite using `[hmk, ← this, mul_comm]`. Use `⟨V * diagonal m * Vᴴ, ?_⟩` and prove the remaining obligations. Establish `h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ`.

Rewrite using `[hA, hC]`. Simplify using `only [Matrix.mul_assoc, hV, Matrix.mul_one]`. Rewrite using `[h1, hDC, hC]`. Simplify using `only [← Matrix.mul_assoc, hU, Matrix.one_mul]`.
-/
theorem trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by
  intro ι _ _ κ _ _ H A Q ⟨U, d, hU, hH, hA⟩ hQ
  have hAh : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose _ ?_
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    exact Complex.conj_ofReal _
  obtain ⟨V, m, hV, hV', hm⟩ := exists_diag _ (Matrix.isHermitian_conjTranspose_mul_mul Q hAh)
  set C : Matrix ι κ ℂ := Uᴴ * Q * V with hC
  have hCH : Cᴴ = Vᴴ * Qᴴ * U := by
    simp [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have key : ∀ D : Matrix ι ι ℂ, Cᴴ * D * C = Vᴴ * (Qᴴ * (U * D * Uᴴ) * Q) * V := by
    intro D
    rw [hCH, hC]
    simp only [Matrix.mul_assoc]
  have hw : ∀ k, ∑ j, Complex.normSq (C j k) = 1 := by
    intro k
    have h := compress_diag C (fun _ => 1) k
    have h1 : diagonal (fun _ : ι => ((1 : ℝ) : ℂ)) = 1 := by simp
    rw [key, h1, Matrix.mul_one, hU, Matrix.mul_one, hQ, Matrix.mul_one, hV'] at h
    simp only [Matrix.one_apply_eq, mul_one] at h
    exact_mod_cast h.symm
  have hmk : ∀ k, m k = ((∑ j, Complex.normSq (C j k) * Real.exp (d j) : ℝ) : ℂ) := by
    intro k
    rw [← compress_diag C (fun j => Real.exp (d j)) k, key, ← hA, hm, Matrix.diagonal_apply_eq]
  have hJ := fun k => jensen_exp (fun j => Complex.normSq (C j k)) d
    (fun j => Complex.normSq_nonneg _) (hw k)
  have hdet : (Qᴴ * A * Q).det.re = ∏ k, ∑ j, Complex.normSq (C j k) * Real.exp (d j) := by
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal] at h
    rw [h]
    simp only [hmk]
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have htr : (Matrix.trace (Qᴴ * H * Q)).re = ∑ k, ∑ j, Complex.normSq (C j k) * d j := by
    have h : Matrix.trace (Cᴴ * diagonal (fun i => (d i : ℂ)) * C) = Matrix.trace (Qᴴ * H * Q) := by
      rw [key, ← hH, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [← h, Matrix.trace]
    simp only [Matrix.diag_apply, compress_diag]
    rw [← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hdet, htr, Real.log_prod (fun k _ => (hJ k).1.ne')]
  refine ⟨Finset.sum_le_sum fun k _ => (hJ k).2.1, fun h => ?_⟩
  have heq := (Finset.sum_eq_sum_iff_of_le fun k _ => (hJ k).2.1).1 h
  have hDC : diagonal (fun i => (Real.exp (d i) : ℂ)) * C = C * diagonal m := by
    ext j k
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h0 : C j k = 0
    · simp [h0]
    · have := (hJ k).2.2 (heq k (Finset.mem_univ _)) j (by simpa using h0)
      rw [hmk, ← this, mul_comm]
  refine ⟨V * diagonal m * Vᴴ, ?_⟩
  have h1 : A * Q = U * (diagonal (fun i => (Real.exp (d i) : ℂ)) * C) * Vᴴ := by
    rw [hA, hC]
    simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
  rw [h1, hDC, hC]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

end GlobalTheory.LogCompress
