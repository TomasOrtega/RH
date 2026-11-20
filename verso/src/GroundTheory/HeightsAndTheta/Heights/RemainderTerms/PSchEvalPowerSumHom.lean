import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Establish `hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw`. Conclude with `hw`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : e.support.Nonempty := by`. Rewrite using `[Finset.nonempty_iff_ne_empty]`.

Introduce `h`. Rewrite `hsum` using `[h, Finset.sum_empty]`. Use linear arithmetic over natural numbers and integers. Establish `hej : 1 ≤ e j` using `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)`. Establish `hjk : k ≤ (j : ℕ) + 1` using `Nat.le_of_dvd (by omega) (hd j hj)`.

Rewrite `hsum` using `[← Finset.add_sum_erase _ _ hj]`. Establish `hmul : k ≤ e j * ((j : ℕ) + 1)` using `le_trans hjk (Nat.le_mul_of_pos_left _ hej)`. Establish `hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0` using `by omega`. Establish `hjm : e j * ((j : ℕ) + 1) = k` using `by omega`. Establish `hej1 : e j = 1` using `by nlinarith`.

Establish `hjv : j = (⟨k - 1, by omega⟩ : Fin N)`. Rewrite `hjm` using `[hej1, one_mul]`. Conclude with `Fin.ext (by simp; omega)`. Establish `hother : ∀ i, i ≠ j → e i = 0`. Introduce `i hij`.

Assume the negation of the conclusion as `hne`. Establish `hi : i ∈ e.support.erase j` using `Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩`. Establish `h0` using `(Finset.sum_eq_zero_iff.mp hrest) i hi`. Rewrite `h0` using `[Nat.mul_eq_zero]`. Use linear arithmetic over natural numbers and integers.

Use extensionality with `i`. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs with h`. Rewrite using `[← h, ← hjv, hej1]`. Conclude with `hother i (fun hij => h (hjv.symm.trans hij.symm))`.
-/
theorem SchEvalPowerSumHom.eq_single_of_dvd {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))

/- English proof (translation)
Introduce `N k hk1 hkN S hS`. Establish `hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) = if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0` using `fun i => h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)`. Establish `hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) = aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S`. Rewrite using `[powerSumHom, ← AlgHom.comp_apply, comp_aeval]`. Rewrite using `[hcomp]`.

Use `conv_lhs => rw [S.as_sum, map_sum]`. Rewrite using `[Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]`. Establish `hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1`. Simplify using `only [Nat.sub_add_cancel hk1, dvd_refl]`. Rewrite using `[aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]`.

Simplify using `[mul_comm]`. Introduce `e he hne`. Rewrite using `[aeval_monomial]`. Establish `hw` using `hS (MvPolynomial.mem_support_iff.mp he)`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)`. Rewrite using `[Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]`. Rewrite using `[hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]`.

Introduce `h`. Rewrite using `[MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]`.
-/
theorem SchEvalPowerSumHom.proof (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]
  conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, if_pos hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, if_neg hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]

end GroundTheory.Heights₂.Heights.RestTerms
