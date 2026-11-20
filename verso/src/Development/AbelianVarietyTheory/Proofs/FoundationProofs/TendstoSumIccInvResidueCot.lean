import Mathlib
open Complex Filter Topology
open scoped Real

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Establish `h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) = insert (-((N:ℤ) + 1)) (insert ((N:ℤ) + 1) (Finset.Icc (-(N:ℤ)) N))`. Use extensionality with `k`.

Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]`. Use `push_cast`.

Simplify using `only [one_div, sub_eq_add_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Finset.mem_Icc, Finset.mem_insert]`.

Use linear arithmetic over natural numbers and integers.
-/
lemma sum_Icc_inv_add_eq_cotTerm (w : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (w + n)⁻¹ =
      1 / w + ∑ j ∈ Finset.range N, (1 / (w - (j + 1)) + 1 / (w + (j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N:ℤ) + 1)) (insert ((N:ℤ) + 1) (Finset.Icc (-(N:ℤ)) N)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [h, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast
      simp only [one_div, sub_eq_add_neg]
      ring
    · simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc, Finset.mem_insert]; omega

/- English proof (translation)
Introduce `L z r hL hz`. Establish `hL0 : (L : ℂ) ≠ 0` using `by exact_mod_cast hL.ne'`. Use `set w : ℂ := (z + r) / L with hw`. Establish `hwL : z + r = w * L` using `by rw [hw]; field_simp`. Establish `hmem : w ∈ Complex.integerComplement`.

Introduce and unpack `⟨k, hk⟩`. Use `congrArg Complex.im hwL` as an intermediate fact. Rewrite `this` using `[← hk]`. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `((tendsto_logDeriv_euler_cot_sub hmem).const_add (1 / w)).const_mul (L : ℂ)⁻¹`. Establish `hlim : (L : ℂ)⁻¹ * (1 / w + (π * Complex.cot (π * w) - 1 / w)) = π / L * Complex.cot (π * w)` using `by ring`. Rewrite `h1` using `[hlim]`. Use `h1.congr fun N => ?_` and prove the remaining obligations. Use `sum_Icc_inv_add_eq_cotTerm w N` as an intermediate fact.

Simplify using `only [cotTerm]`. Rewrite using `[← this, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[hwL, ← add_mul, mul_inv, mul_comm]`.
-/
theorem tendsto_sum_Icc_inv_residue_cot :
    ∀ (L : ℕ) (z : ℂ) (r : ℕ), 0 < L → 0 < z.im →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, (z + r + n * L)⁻¹) atTop
        (𝓝 (π / L * Complex.cot (π * ((z + r) / L)))) := by
  intro L z r hL hz
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set w : ℂ := (z + r) / L with hw
  have hwL : z + r = w * L := by rw [hw]; field_simp
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hwL
    rw [← hk] at this
    simp at this
    linarith
  have h1 := ((tendsto_logDeriv_euler_cot_sub hmem).const_add (1 / w)).const_mul (L : ℂ)⁻¹
  have hlim : (L : ℂ)⁻¹ * (1 / w + (π * Complex.cot (π * w) - 1 / w)) =
      π / L * Complex.cot (π * w) := by ring
  rw [hlim] at h1
  refine h1.congr fun N => ?_
  have := sum_Icc_inv_add_eq_cotTerm w N
  simp only [cotTerm]
  rw [← this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hwL, ← add_mul, mul_inv, mul_comm]

end GlobalTheory
