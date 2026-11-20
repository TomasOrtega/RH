import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open Polynomial PeriodPair

namespace GlobalTheory

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_associated_pow_of_mul_eq_pow' hc h`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`. Conclude with `hD.ne_zero (by simpa using hd.symm)`. Use `⟨normalize d, monic_normalize hd0, ?_⟩` and prove the remaining obligations.

Use `eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_` and prove the remaining obligations. Conclude with `hd.symm.trans ((associated_normalize d).pow_pow)`.
-/
lemma exists_monic_sq_eq_of_mul_eq_sq {D G P : ℂ[X]} (hD : D.Monic) (hc : IsCoprime D G)
    (h : D * G = P ^ 2) : ∃ h : ℂ[X], h.Monic ∧ D = h ^ 2 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hc h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD.ne_zero (by simpa using hd.symm)
  refine ⟨normalize d, monic_normalize hd0, ?_⟩
  refine eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_
  exact hd.symm.trans ((associated_normalize d).pow_pow)

/- English proof (translation)
Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : ((2 * m + 1 : ℕ) : ℂ) = 0`. Use `push_cast`. Take the linear combination `hα2`.

Conclude with `absurd (Nat.cast_eq_zero.mp h0) (by omega)`. Take `⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩` from `exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk`. Use `set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF`. Use `set n : ℂ[X] := C (α ^ 2) * A with hn`. Establish `hα20 : α ^ 2 ≠ 0` using `pow_ne_zero 2 hα0`.

Establish `hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4`. Introduce `z hz`. Rewrite using `[L.derivWeierstrassP_sq z hz]`. Simplify using `only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnD : IsCoprime n D`. Rewrite using `[hn]`. Conclude with `(isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5`. Establish `key : F * (derivative n * D - n * derivative D) ^ 2 = D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3)`. Use `mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)` and prove the remaining obligations.

Take `⟨z, hz, rfl⟩` from `exists_weierstrassP_eq L x`. Distinguish the cases in `h0 : D.eval (℘[L] z) = 0`. Simplify using `[h0]`. Establish `hz'` using `(c8 z hz).not.mp h0`. Establish `e1` using `derivWeierstrassP_mul_eq hα c9 hz' h0`.

Establish `e2` using `L.derivWeierstrassP_sq _ hz'`. Rewrite `e2` using `[c9 z hz']`. Rewrite using `[eval_mul, eval_mul, eval_mul (p := D), hFe z hz]`. Use `congr 1`. Simplify using `only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C, zero_mul, zero_add] at e1 ⊢`.

Establish `e3` using `congrArg (· ^ 2) e1`. Simplify using `only [mul_pow] at e3`. Rewrite `e3` using `[e2]`. Clear denominators, using `at e3` for the nonvanishing conditions. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(-1 : ℂ) * e3`. Establish `hDF : IsCoprime D F`. Rewrite using `[Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]`. Introduce `x`. Take `⟨z, hz, rfl⟩` from `exists_weierstrassP_eq L x`.

Use `by_contra! hc`. Simplify using `only [coe_aeval_eq_eval] at hc`. Establish `h1` using `(c8 z hz).mp hc.1`. Establish `h2 : ℘'[L] z = 0`. Use `hc.2` as an intermediate fact.

Rewrite `this` using `[hFe z hz]`. Simplify using `using this`. Rewrite `h2` using `[derivWeierstrassP_eq_zero_iff L hz]`. Use `hz ?_` and prove the remaining obligations. Establish `h3` using `sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[nsmul_eq_mul]`. Take the linear combination `z * hα2`. Establish `hDG : IsCoprime D (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3)`. Establish `: n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 = n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2)` using `by ring`.

Rewrite using `[this]`. Conclude with `(hnD.symm.pow_right).add_mul_left_right _`. Take `⟨h, hm, hD⟩` from `exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF) (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)`. Establish `hdn : n.natDegree = 2 * m + 1` using `by rw [hn, natDegree_C_mul hα20, c6, hind]`. Use `⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]`. Rewrite `c7` using `[c6, hind, hD, natDegree_pow]`. Use linear arithmetic over natural numbers and integers. Rewrite `hnD` using `[hD]`. Conclude with `(IsCoprime.pow_right_iff (by norm_num)).mp hnD`.

Rewrite using `[hn, coeff_C_mul]`. Conclude with `mul_mem (pow_mem hαk 2) (c1 i)`. Take `⟨z, hz, rfl⟩` from `exists_weierstrassP_eq L x`. Use `⟨z, hz, (c8 z hz).mp ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hD, eval_pow, hx.eq_zero]`.

Evaluate the numerical expressions. Use `mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_` and prove the remaining obligations. Rewrite `key` using `[hD, derivative_sq]`. Establish `h2 : (C 2 : ℂ[X]) = 2` using `rfl`. Rewrite `key` using `[h2]`.

Take the linear combination `key`.
-/
theorem exists_mul_sqrt_neg_odd_polynomial_identity (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination hα2
    exact absurd (Nat.cast_eq_zero.mp h0) (by omega)
  obtain ⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF
  set n : ℂ[X] := C (α ^ 2) * A with hn
  have hα20 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα0
  have hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4 := by
    intro z hz
    rw [L.derivWeierstrassP_sq z hz]
    simp only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have hnD : IsCoprime n D := by
    rw [hn]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5
  have key : F * (derivative n * D - n * derivative D) ^ 2 =
      D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    refine mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_cases h0 : D.eval (℘[L] z) = 0
    · simp [h0]
    have hz' := (c8 z hz).not.mp h0
    have e1 := derivWeierstrassP_mul_eq hα c9 hz' h0
    have e2 := L.derivWeierstrassP_sq _ hz'
    rw [c9 z hz'] at e2
    rw [eval_mul, eval_mul, eval_mul (p := D), hFe z hz]
    congr 1
    simp only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C,
      zero_mul, zero_add] at e1 ⊢
    have e3 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e3
    rw [e2] at e3
    field_simp at e3
    field_simp
    linear_combination (-1 : ℂ) * e3
  have hDF : IsCoprime D F := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro x
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_contra! hc
    simp only [coe_aeval_eq_eval] at hc
    have h1 := (c8 z hz).mp hc.1
    have h2 : ℘'[L] z = 0 := by
      have := hc.2
      rw [hFe z hz] at this
      simpa using this
    rw [derivWeierstrassP_eq_zero_iff L hz] at h2
    refine hz ?_
    have h3 := sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)
    convert h3 using 1
    rw [nsmul_eq_mul]
    linear_combination z * hα2
  have hDG : IsCoprime D
      (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    have : n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 =
        n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2) := by ring
    rw [this]
    exact (hnD.symm.pow_right).add_mul_left_right _
  obtain ⟨h, hm, hD⟩ := exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF)
    (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)
  have hdn : n.natDegree = 2 * m + 1 := by rw [hn, natDegree_C_mul hα20, c6, hind]
  refine ⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]
  · rw [c6, hind, hD, natDegree_pow] at c7
    omega
  · rw [hD] at hnD
    exact (IsCoprime.pow_right_iff (by norm_num)).mp hnD
  · rw [hn, coeff_C_mul]
    exact mul_mem (pow_mem hαk 2) (c1 i)
  · obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    refine ⟨z, hz, (c8 z hz).mp ?_, rfl⟩
    rw [hD, eval_pow, hx.eq_zero]
    norm_num
  · refine mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_
    rw [hD, derivative_sq] at key
    have h2 : (C 2 : ℂ[X]) = 2 := rfl
    rw [h2] at key
    linear_combination key

end GlobalTheory
