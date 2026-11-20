import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def expN (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range (N + 1), z ^ n / (n.factorial : ℂ)

def gN (N : ℕ) (z : ℂ) : ℂ := cexp z - expN N z

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => show HasDerivAt (expN 1) (expN 0 z) z`. Establish `h0 : expN 1 = fun w => 1 + w`. Use function extensionality and compare the values at `w`. Simplify using `[expN, Finset.sum_range_succ]`.

Establish `h1 : expN 0 z = 1` using `by simp [expN]`. Rewrite using `[h0, h1]`. Conclude with `(hasDerivAt_id z).const_add 1`. Consider the case `succ N ih`. Establish `hf : expN (N + 1 + 1) = fun w => expN (N + 1) w + w ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℂ)`.

Use function extensionality and compare the values at `w`. Simplify using `only [expN]`. Conclude with `Finset.sum_range_succ _ (N + 1 + 1)`. Rewrite using `[hf]`. Establish `h2` using `ih.add ((hasDerivAt_pow (N + 1 + 1) z).div_const ((N + 1 + 1).factorial : ℂ))`.

Use `h2.congr_deriv ?_` and prove the remaining obligations. Establish `hf1 : ((N + 1).factorial : ℂ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero (N + 1)`. Establish `hne : ((N + 1 + 1 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero (N + 1)`. Simplify using `only [expN, Finset.sum_range_succ _ (N + 1), Nat.factorial_succ (N + 1), Nat.add_sub_cancel]`. Use `first`.

Consider the case `(congr 1; rw [Nat.cast_mul]; exact mul_div_mul_left _ _ hne)`. Consider the case `(push_cast; field_simp; ring)`. Consider the case `(push_cast; field_simp)`.
-/
theorem expN_hasDerivAt (N : ℕ) (z : ℂ) : HasDerivAt (expN (N + 1)) (expN N z) z := by
  induction N with
  | zero =>
    show HasDerivAt (expN 1) (expN 0 z) z
    have h0 : expN 1 = fun w => 1 + w := by
      funext w; simp [expN, Finset.sum_range_succ]
    have h1 : expN 0 z = 1 := by simp [expN]
    rw [h0, h1]
    exact (hasDerivAt_id z).const_add 1
  | succ N ih =>
    have hf : expN (N + 1 + 1) = fun w => expN (N + 1) w + w ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℂ) := by
      funext w; simp only [expN]; exact Finset.sum_range_succ _ (N + 1 + 1)
    rw [hf]
    have h2 := ih.add ((hasDerivAt_pow (N + 1 + 1) z).div_const ((N + 1 + 1).factorial : ℂ))
    refine h2.congr_deriv ?_
    have hf1 : ((N + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
    have hne : ((N + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    simp only [expN, Finset.sum_range_succ _ (N + 1), Nat.factorial_succ (N + 1), Nat.add_sub_cancel]
    first
      | (congr 1; rw [Nat.cast_mul]; exact mul_div_mul_left _ _ hne)
      | (push_cast; field_simp; ring)
      | (push_cast; field_simp)

/- English proof (translation)
Unfold `expN`. Use `first`. Consider the case `exact ContDiff.sum fun n _ => (contDiff_id.pow n).div_const _`. Consider the case `fun_prop`.
-/
theorem contDiff_expN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (expN N) := by
  unfold expN
  first
    | exact ContDiff.sum fun n _ => (contDiff_id.pow n).div_const _
    | fun_prop

/- English proof (translation)
Unfold `gN`. Conclude with `Complex.contDiff_exp.sub (contDiff_expN N)`.
-/
theorem contDiff_gN (N : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (gN N) := by
  unfold gN
  exact Complex.contDiff_exp.sub (contDiff_expN N)

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `h : HasDerivAt (gN (N + 1)) (cexp z - expN N z) z`. Unfold `gN`. Conclude with `(Complex.hasDerivAt_exp z).sub (expN_hasDerivAt N z)`. Rewrite using `[h.deriv]`.

Both sides reduce to the same expression.
-/
theorem deriv_gN (N : ℕ) : deriv (gN (N + 1)) = gN N := by
  funext z
  have h : HasDerivAt (gN (N + 1)) (cexp z - expN N z) z := by
    unfold gN
    exact (Complex.hasDerivAt_exp z).sub (expN_hasDerivAt N z)
  rw [h.deriv]
  rfl

/- English proof (translation)
Simplify using `[gN, expN, Finset.sum_range_succ']`.
-/
theorem gN_zero (N : ℕ) : gN N 0 = 0 := by
  simp [gN, expN, Finset.sum_range_succ']

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro N _`. Rewrite using `[iteratedDeriv_zero]`. Conclude with `gN_zero N`.

Consider the case `succ i ih`. Introduce `N hN`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `⟨N - 1, by omega⟩`. Rewrite using `[iteratedDeriv_succ', deriv_gN]`. Conclude with `ih M (by omega)`.
-/
theorem iteratedDeriv_gN : ∀ i N : ℕ, i ≤ N → iteratedDeriv i (gN N) 0 = 0 := by
  intro i
  induction i with
  | zero => intro N _; rw [iteratedDeriv_zero]; exact gN_zero N
  | succ i ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [iteratedDeriv_succ', deriv_gN]
    exact ih M (by omega)

def ellL (q : ℕ) (a : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  ((q : ℂ) * (Real.pi : ℂ)) • innerSL ℂ a

/- English proof (translation)
Simplify using `[ellL, Hf]`. Use `left`. Use `first`. Consider the case `(rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm])`. Consider the case `(simp [PiLp.inner_apply, mul_comm]; done)`.

Consider the case `(simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]; done)`.
-/
theorem ellL_apply (q : ℕ) (a v : EuclideanSpace ℂ ι) : ellL q a v = q * Real.pi * Hf v a := by
  simp [ellL, Hf]
  left
  first
    | (rw [PiLp.inner_apply]; exact Finset.sum_congr rfl fun x _ => by simp [mul_comm])
    | (simp [PiLp.inner_apply, mul_comm]; done)
    | (simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]; done)

/- English proof (translation)
Establish `hg : ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v))` using `(contDiff_gN N).comp (ellL q a).contDiff`. Establish `hz : ∀ i, i ≤ N → ‖iteratedFDeriv ℂ i (fun v => gN N (ellL q a v)) 0‖ = 0`. Introduce `i hi`. Apply the tactic sequence `have h1 := (ellL q a).iteratedFDeriv_comp_right (contDiff_gN N) (0 : EuclideanSpace ℂ ι) (i := i) (by first | exact le_top | exact WithTop.coe_le_coe.mpr le_top | exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤) | simp)`. Establish `h2 : iteratedFDeriv ℂ i (gN N) 0 = 0`.

Rewrite using `[← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gN i N hi, norm_zero]`. Rewrite `h1` using `[map_zero, h2]`. Rewrite using `[show (fun v => gN N (ellL q a v)) = gN N ∘ ellL q a from rfl, h1, norm_eq_zero]`. Use extensionality with `m`. Simplify using the standard rewrite rules.

Apply the tactic sequence `refine norm_le_zero_iff.mp ((norm_iteratedFDeriv_mul_le hg hP 0 (by first | exact le_top | simp | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).trans_eq ?_)`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hz i (by have := Finset.mem_range.mp hi; omega)]`. Simplify using the standard rewrite rules.
-/
theorem iteratedFDeriv_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℂ k (fun v => gN N (ellL q a v) * P v) 0 = 0 := by
  have hg : ContDiff ℂ (⊤ : ℕ∞) (fun v => gN N (ellL q a v)) := (contDiff_gN N).comp (ellL q a).contDiff
  have hz : ∀ i, i ≤ N → ‖iteratedFDeriv ℂ i (fun v => gN N (ellL q a v)) 0‖ = 0 := by
    intro i hi
    have h1 := (ellL q a).iteratedFDeriv_comp_right (contDiff_gN N) (0 : EuclideanSpace ℂ ι)
      (i := i) (by first | exact le_top | exact WithTop.coe_le_coe.mpr le_top | exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤) | simp)
    have h2 : iteratedFDeriv ℂ i (gN N) 0 = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_gN i N hi, norm_zero]
    rw [map_zero, h2] at h1
    rw [show (fun v => gN N (ellL q a v)) = gN N ∘ ellL q a from rfl, h1, norm_eq_zero]
    ext m
    simp
  refine norm_le_zero_iff.mp ((norm_iteratedFDeriv_mul_le hg hP 0
    (by first | exact le_top | simp | exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).trans_eq ?_)
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hz i (by have := Finset.mem_range.mp hi; omega)]
  simp

/- English proof (translation)
Unfold `paD polyDeriv`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hmα : m = α` using `by first`. Consider the case `(simp [MvPolynomial.support_monomial] at hm; exact hm)`. Consider the case `(rw [MvPolynomial.support_monomial] at hm; split_ifs at hm with h`.

Simplify using `at hm`. Simplify using `using hm)`. Substitute `hmα` using the available equality. Establish `hk : Multiset.card (Finsupp.toMultiset m) ≤ N`. Rewrite using `[Finsupp.card_toMultiset]`.

Use `first`. Consider the case `exact hα`. Consider the case `simpa [Finsupp.degree, Finsupp.sum] using hα`. Rewrite using `[iteratedFDeriv_tail_zero q a N hP hk]`. Simplify using the standard rewrite rules.
-/
theorem paD_tail_zero (q : ℕ) (a : EuclideanSpace ℂ ι) (N : ℕ) {P : EuclideanSpace ℂ ι → ℂ}
    (hP : ContDiff ℂ (⊤ : ℕ∞) P) {α : ι →₀ ℕ} (hα : α.degree ≤ N) :
    paD α (fun v => gN N (ellL q a v) * P v) = 0 := by
  unfold paD polyDeriv
  refine Finset.sum_eq_zero fun m hm => ?_
  have hmα : m = α := by
    first
      | (simp [MvPolynomial.support_monomial] at hm; exact hm)
      | (rw [MvPolynomial.support_monomial] at hm; split_ifs at hm with h
         · simp at hm
         · simpa using hm)
  subst hmα
  have hk : Multiset.card (Finsupp.toMultiset m) ≤ N := by
    rw [Finsupp.card_toMultiset]
    first
      | exact hα
      | simpa [Finsupp.degree, Finsupp.sum] using hα
  rw [iteratedFDeriv_tail_zero q a N hP hk]
  simp

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
