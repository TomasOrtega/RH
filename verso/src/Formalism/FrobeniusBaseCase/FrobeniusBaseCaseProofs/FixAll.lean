import Formalism.FrobeniusBaseCase.StatementFix
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.BaseCaseFalseGeneralHolds

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

/- English proof (translation)
Establish `hl : (3 : ℝ) ≤ (D.l : ℝ)` using `by exact_mod_cast D.l_ge`. Establish `h1` using `identity_twenty_d D.l D.i (by have := D.l_ge; omega) D.i_odd`. Establish `hq1 : (1 : ℝ) ≤ qnum D.l` using `by unfold qnum; nlinarith`. Establish `hsg : 0 < sg D.l D.i` using `by unfold sg; positivity`. Establish `h2 : qnum D.l ^ (s + 1) ≤ qnum D.l ^ Kn D.i` using `pow_le_pow_right₀ hq1 hsK`.

Establish `h3 : qnum D.l ^ (s + 1) * sg D.l D.i ≤ 3 * (D.l : ℝ) / 8`. Rewrite using `[← h1]`. Conclude with `mul_le_mul_of_nonneg_right h2 hsg.le`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_lt]`.

Establish `h4 : qnum D.l ^ (s + 1) * sg D.l D.i = (qnum D.l ^ s * sg D.l D.i) * qnum D.l`. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[h4]`. Establish `h5 : qnum D.l ≤ (qnum D.l ^ s * sg D.l D.i) * qnum D.l` using `by nlinarith`.

Unfold `qnum at h5 h3`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem qs_sigma_lt_one (s : ℕ) (hsK : s < D.K) : qnum D.l ^ s * sg D.l D.i < 1 := by
  have hl : (3 : ℝ) ≤ (D.l : ℝ) := by exact_mod_cast D.l_ge
  have h1 := identity_twenty_d D.l D.i (by have := D.l_ge; omega) D.i_odd
  have hq1 : (1 : ℝ) ≤ qnum D.l := by unfold qnum; nlinarith
  have hsg : 0 < sg D.l D.i := by unfold sg; positivity
  have h2 : qnum D.l ^ (s + 1) ≤ qnum D.l ^ Kn D.i := pow_le_pow_right₀ hq1 hsK
  have h3 : qnum D.l ^ (s + 1) * sg D.l D.i ≤ 3 * (D.l : ℝ) / 8 := by
    rw [← h1]; exact mul_le_mul_of_nonneg_right h2 hsg.le
  by_contra hcon
  rw [not_lt] at hcon
  have h4 : qnum D.l ^ (s + 1) * sg D.l D.i = (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by
    rw [pow_succ]; ring
  rw [h4] at h3
  have h5 : qnum D.l ≤ (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by nlinarith
  unfold qnum at h5 h3
  nlinarith

/- English proof (translation)
Establish `h` using `(identity_e D.l s (by have := D.l_ge; omega)).2.2`. Establish `hl1 : 1 ≤ D.l ^ 2` using `Nat.one_le_pow _ _ D.l_prime.pos`. Establish `hR : (eNum D.l s : ℝ) * ((D.l : ℝ) ^ 2 - 1) + 1 = ((D.l : ℝ) ^ 2) ^ s`. Establish `h' : ((eNum D.l s * (D.l ^ 2 - 1) + 1 : ℕ) : ℝ) = (((D.l ^ 2) ^ s : ℕ) : ℝ)` using `by rw [h]`. Move the coercions through the operations in `[Nat.cast_sub hl1] at h'`.

Conclude with `h'`. Establish `hm` using `rho_mul D.l_ge`. Unfold `qnum`. Rewrite using `[← hR]`. Take the linear combination `(eNum D.l s : ℝ) * hm`.
-/
theorem e_real (s : ℕ) : qnum D.l ^ s * rho D.l - (eNum D.l s : ℝ) = rho D.l := by
  have h := (identity_e D.l s (by have := D.l_ge; omega)).2.2
  have hl1 : 1 ≤ D.l ^ 2 := Nat.one_le_pow _ _ D.l_prime.pos
  have hR : (eNum D.l s : ℝ) * ((D.l : ℝ) ^ 2 - 1) + 1 = ((D.l : ℝ) ^ 2) ^ s := by
    have h' : ((eNum D.l s * (D.l ^ 2 - 1) + 1 : ℕ) : ℝ) = (((D.l ^ 2) ^ s : ℕ) : ℝ) := by rw [h]
    push_cast [Nat.cast_sub hl1] at h'
    exact h'
  have hm := rho_mul D.l_ge
  unfold qnum
  rw [← hR]
  linear_combination (eNum D.l s : ℝ) * hm

/- English proof (translation)
Introduce `s hs1 hsK c hc P hP d hu h`. Establish `h1` using `h.1 c (by rw [hc]; exact hsK)`. Rewrite `h1` using `[hc, D.zvec_eq_zero (by omega), zero_sub]`. Establish `h2` using `h1 (Finsupp.single d (D.q ^ s))`. Establish `hq0 : D.q ^ s ≠ 0` using `pow_ne_zero _ (by have := D.q_pos; omega)`.

Establish `hcoef : coeff (Finsupp.single d (D.q ^ s)) (D.m s c) = ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) * P d`. Rewrite using `[hP, coeff_C_mul, coeff_sum_C_mul_X_pow]`. Simplify using `only [Finsupp.single_left_inj hq0]`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.

Establish `hvl : D.v (((D.l : k) ^ eNum D.l s)⁻¹) = ((-(eNum D.l s : ℝ) : ℝ) : WithTop ℝ)`. Rewrite using `[← inv_pow]`. Generalize the expression as in `eNum D.l s = e`. Proceed by induction on `e with`. Consider the case `zero => simp`.

Consider the case `succ e ih`. Rewrite using `[pow_succ, AddValuation.map_mul, ih, D.v_l_inv, ← WithTop.coe_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsign : D.v ((-1 : k) ^ s) = 0`. Apply the tactic sequence `rcases neg_one_pow_eq_or k s with h | h <;> rw [h] <;> simp [AddValuation.map_neg]`. Rewrite `h2` using `[map_neg, AddValuation.map_neg, hcoef, AddValuation.map_mul, AddValuation.map_mul, hsign, hvl, hu, zero_add, add_zero, Finsupp.degree_single, ← WithTop.coe_add, WithTop.coe_le_coe]`. Establish `h3` using `D.qs_sigma_lt_one s hsK`. Establish `h4` using `D.e_real s`.

Establish `h5 : ((D.q ^ s : ℕ) : ℝ) = qnum D.l ^ s`. Rewrite using `[Nat.cast_pow, D.q_cast]`. Rewrite `h2` using `[h5]`. Unfold `Data.top Data.rad at h2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem unit_entry_all : D.UnitEntryAll := by
  intro s hs1 hsK c hc P hP d hu h
  have h1 := h.1 c (by rw [hc]; exact hsK)
  rw [hc, D.zvec_eq_zero (by omega), zero_sub] at h1
  have h2 := h1 (Finsupp.single d (D.q ^ s))
  have hq0 : D.q ^ s ≠ 0 := pow_ne_zero _ (by have := D.q_pos; omega)
  have hcoef : coeff (Finsupp.single d (D.q ^ s)) (D.m s c)
      = ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) * P d := by
    rw [hP, coeff_C_mul, coeff_sum_C_mul_X_pow]
    simp only [Finsupp.single_left_inj hq0]
    rw [Finset.sum_ite_eq]
    simp
  have hvl : D.v (((D.l : k) ^ eNum D.l s)⁻¹) = ((-(eNum D.l s : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← inv_pow]
    generalize eNum D.l s = e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ, AddValuation.map_mul, ih, D.v_l_inv, ← WithTop.coe_add]
      congr 1
      push_cast
      ring
  have hsign : D.v ((-1 : k) ^ s) = 0 := by
    rcases neg_one_pow_eq_or k s with h | h <;> rw [h] <;> simp [AddValuation.map_neg]
  rw [map_neg, AddValuation.map_neg, hcoef, AddValuation.map_mul, AddValuation.map_mul, hsign, hvl,
    hu, zero_add, add_zero, Finsupp.degree_single, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
  have h3 := D.qs_sigma_lt_one s hsK
  have h4 := D.e_real s
  have h5 : ((D.q ^ s : ℕ) : ℝ) = qnum D.l ^ s := by
    rw [Nat.cast_pow, D.q_cast]
  rw [h5] at h2
  unfold Data.top Data.rad at h2
  nlinarith

/- English proof (translation)
Introduce `hm`. Use function extensionality and compare the values at `c`. Unfold `start`. Use `split_ifs with h`. Break down `Nat.eq_zero_or_pos (D.lev c) with h0 | h0` into its components or cases.

Rewrite using `[h0]`. Both sides reduce to the same expression. Rewrite using `[hm (D.lev c) c h0 h rfl, D.zvec_eq_zero (by omega)]`. Rewrite using `[D.zvec_eq_zero (by have := D.K_pos; omega)]`.
-/
theorem start_eq_z : D.StartEqZ := by
  intro hm
  funext c
  unfold start
  split_ifs with h
  · rcases Nat.eq_zero_or_pos (D.lev c) with h0 | h0
    · rw [h0]; rfl
    · rw [hm (D.lev c) c h0 h rfl, D.zvec_eq_zero (by omega)]
  · rw [D.zvec_eq_zero (by have := D.K_pos; omega)]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => coeff_C_mul _ _ _`.
-/
theorem coeff_logSum (t : C → MvPowerSeries Z k) (b : C) (A : Z →₀ ℕ) (N : ℕ) :
    coeff A (∑ c, ∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j)) =
      ∑ c, ∑ j ∈ Finset.Icc 1 N, D.al c j b * coeff A (t c ^ (D.l ^ j)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => coeff_C_mul _ _ _

/- English proof (translation)
Introduce `t ht`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `b`. Use extensionality with `A`.

Rewrite using `[D.opIsLimit t ht b A A.degree le_rfl, coeff_PsiPartial]`. Use `h b A A.degree le_rfl` as an intermediate fact. Rewrite `this` using `[map_add, coeff_logSum]`. Take the linear combination `-this`. Introduce `h b A N hN`.

Use `D.opIsLimit t ht b A N hN` as an intermediate fact. Rewrite `this` using `[h, coeff_PsiPartial]`. Rewrite using `[map_add, coeff_logSum]`. Take the linear combination `this`.
-/
theorem LogIffFix_statement : D.LogIffFix := by
  intro t ht
  constructor
  · intro h
    funext b
    ext A
    rw [D.opIsLimit t ht b A A.degree le_rfl, coeff_PsiPartial]
    have := h b A A.degree le_rfl
    rw [map_add, coeff_logSum] at this
    linear_combination -this
  · intro h b A N hN
    have := D.opIsLimit t ht b A N hN
    rw [h, coeff_PsiPartial] at this
    rw [map_add, coeff_logSum]
    linear_combination this

/- English proof (translation)
Take `⟨t, ⟨h0, h1⟩, huniq⟩` from `D.hasUniqueFixedPoint.1`. Conclude with `⟨t, ⟨h0, (D.LogIffFix_statement t h0).2 h1⟩, fun t' ht' => huniq t' ⟨ht'.1, (D.LogIffFix_statement t' ht'.1).1 ht'.2⟩⟩`.
-/
theorem log_unique_bis : D.LogUnique := by
  obtain ⟨t, ⟨h0, h1⟩, huniq⟩ := D.hasUniqueFixedPoint.1
  exact ⟨t, ⟨h0, (D.LogIffFix_statement t h0).2 h1⟩,
    fun t' ht' => huniq t' ⟨ht'.1, (D.LogIffFix_statement t' ht'.1).1 ht'.2⟩⟩

/- English proof (translation)
Introduce `t h0 h1` and use `D.chainII_holds t h0 ((D.LogIffFix_statement t h0).1 h1)`.
-/
theorem chain_ii_of_log : D.ChainIILog :=
  fun t h0 h1 => D.chainII_holds t h0 ((D.LogIffFix_statement t h0).1 h1)

end Data

end

end Formalism.BaseCaseIdentities
