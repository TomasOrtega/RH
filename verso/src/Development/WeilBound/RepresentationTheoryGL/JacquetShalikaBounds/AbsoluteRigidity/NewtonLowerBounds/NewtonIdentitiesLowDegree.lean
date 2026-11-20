import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open MvPolynomial Finset

namespace PositivityTheory.RgJS.NewtonIdentitiesAlt

variable {A : Type} [Fintype A]

def ev (a : A → ℂ) (j : ℕ) : ℂ := ∑ t ∈ powersetCard j (univ : Finset A), ∏ i ∈ t, a i

/- English proof (translation)
Simplify using `[esymm, ev, map_sum, map_prod]`.
-/
theorem aeval_esymm (a : A → ℂ) (j : ℕ) : aeval a (esymm A ℂ j) = ev a j := by
  simp [esymm, ev, map_sum, map_prod]

/- English proof (translation)
Simplify using `[ev]`.
-/
theorem ev_zero (a : A → ℂ) : ev a 0 = 1 := by simp [ev]

/- English proof (translation)
Rewrite using `[ev, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]`.
-/
theorem ev_card (a : A → ℂ) : ev a (Fintype.card A) = ∏ i, a i := by
  rw [ev, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]

/- English proof (translation)
Establish `h` using `congrArg (aeval a) (MvPolynomial.mul_esymm_eq_sum A ℂ j)`. Simplify `h` using `[map_mul, map_sum, aeval_esymm, MvPolynomial.psum]`.
-/
theorem newton [DecidableEq A] (a : A → ℂ) (j : ℕ) :
    (j : ℂ) * ev a j = (-1) ^ (j + 1) *
      ∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2 := by
  have h := congrArg (aeval a) (MvPolynomial.mul_esymm_eq_sum A ℂ j)
  simpa [map_mul, map_sum, aeval_esymm, MvPolynomial.psum] using h

omit [Fintype A] in
/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hx`. Simplify using `only [Finset.coe_range, Set.mem_Iio]`. Conclude with `hx.2)`. Use the proof step `(fun x hx y hy hxy => by`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy`. Establish `e1` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1`. Establish `e2` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hy.1`. Conclude with `Prod.ext hxy (by omega))`. Use `_ = j := Finset.card_range j`.
-/
theorem card_filter_lt (j : ℕ) : #{x ∈ antidiagonal j | x.1 < j} ≤ j := by
  calc #{x ∈ antidiagonal j | x.1 < j} ≤ #(range j) :=
        Finset.card_le_card_of_injOn Prod.fst
          (fun x hx => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
            simp only [Finset.coe_range, Set.mem_Iio]
            exact hx.2)
          (fun x hx y hy hxy => by
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
            have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
            have e2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hy.1
            exact Prod.ext hxy (by omega))
    _ = j := Finset.card_range j

/- English proof (translation)
Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `hj1 hjN`. Establish `hev : ∀ m, m < j → ‖ev a m‖ ≤ 1` using `fun m hm => by`.

Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite using `[ev_zero]`. Simplify using the standard rewrite rules. Conclude with `(ih m hm h (by omega)).trans hδ`.

Establish `hsum : ‖∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ ≤ j * δ`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [Finset.mem_filter] at hx`.

Establish `e1` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1`. Rewrite using `[norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = (#{x ∈ antidiagonal j | x.1 < j} : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ j * δ := by gcongr`.

Conclude with `card_filter_lt j` after adjusting the coercions. Establish `h2 : (j : ℝ) * ‖ev a j‖ ≤ j * δ`. Establish `h3` using `congrArg norm (newton a j)`. Rewrite `h3` using `[norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]`. Rewrite using `[h3]`.

Conclude with `hsum`. Establish `hjpos : (0 : ℝ) < j` using `by exact_mod_cast hj1`. Conclude with `le_of_mul_le_mul_left h2 hjpos`.
-/
theorem bound [DecidableEq A] (a : A → ℂ) (N : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ δ) : ∀ j, 1 ≤ j → j ≤ N → ‖ev a j‖ ≤ δ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj1 hjN
  have hev : ∀ m, m < j → ‖ev a m‖ ≤ 1 := fun m hm => by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [ev_zero]
      simp
    · exact (ih m hm h (by omega)).trans hδ
  have hsum : ‖∑ x ∈ antidiagonal j with x.1 < j, (-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ ≤ j * δ := by
    calc _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, ‖(-1) ^ x.1 * ev a x.1 * ∑ i, a i ^ x.2‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ antidiagonal j with x.1 < j, δ := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        have e1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hx.1
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        calc ‖ev a x.1‖ * ‖∑ i, a i ^ x.2‖ ≤ 1 * δ :=
              mul_le_mul (hev _ hx.2) (hp _ (by omega) (by omega)) (norm_nonneg _) zero_le_one
          _ = δ := one_mul δ
      _ = (#{x ∈ antidiagonal j | x.1 < j} : ℝ) * δ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ j * δ := by
        gcongr
        exact_mod_cast card_filter_lt j
  have h2 : (j : ℝ) * ‖ev a j‖ ≤ j * δ := by
    have h3 := congrArg norm (newton a j)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at h3
    rw [h3]
    exact hsum
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  exact le_of_mul_le_mul_left h2 hjpos

end PositivityTheory.RgJS.NewtonIdentitiesAlt

namespace PositivityTheory.RgJS

open NewtonIdentitiesAlt in
/- English proof (translation)
Introduce `N hN`. Use `⟨1 / 4, by norm_num, fun A _ a hA hprod => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ 1 / 2`.

Introduce `k hk1 hkN`. Assume the negation of the conclusion as `hk`. Use `push_neg at hk`. Establish `hle : ‖∑ i, a i ^ k‖ ^ 2 ≤ ∑ m ∈ range N, ‖∑ i, a i ^ (m + 1)‖ ^ 2`. Establish `hmem : k - 1 ∈ range N`.

Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `Finset.single_le_sum (f := fun m => ‖∑ i, a i ^ (m + 1)‖ ^ 2) (fun m _ => by positivity) hmem`. Simplify `h4` using `[Nat.sub_add_cancel hk1]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h5` using `bound a N (1 / 2) (by norm_num) (by norm_num) hp N hN le_rfl`. Rewrite `h5` using `[← hA, ev_card, hprod]`. Evaluate the numerical expressions using `at h5`.
-/
theorem newton_identities_low_degree : NewtonLow := by
  intro N hN
  refine ⟨1 / 4, by norm_num, fun A _ a hA hprod => ?_⟩
  classical
  by_contra hlt
  push_neg at hlt
  have hp : ∀ k, 1 ≤ k → k ≤ N → ‖∑ i, a i ^ k‖ ≤ 1 / 2 := by
    intro k hk1 hkN
    by_contra hk
    push_neg at hk
    have hle : ‖∑ i, a i ^ k‖ ^ 2 ≤ ∑ m ∈ range N, ‖∑ i, a i ^ (m + 1)‖ ^ 2 := by
      have hmem : k - 1 ∈ range N := by
        rw [Finset.mem_range]
        omega
      have h4 := Finset.single_le_sum (f := fun m => ‖∑ i, a i ^ (m + 1)‖ ^ 2) (fun m _ => by positivity) hmem
      simpa [Nat.sub_add_cancel hk1] using h4
    nlinarith
  have h5 := bound a N (1 / 2) (by norm_num) (by norm_num) hp N hN le_rfl
  rw [← hA, ev_card, hprod] at h5
  norm_num at h5

end PositivityTheory.RgJS
