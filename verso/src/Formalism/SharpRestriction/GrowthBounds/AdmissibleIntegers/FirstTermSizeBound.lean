import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

/- English proof (translation)
Use `haveI := Fact.mk hp`. Rewrite using `[Nat.factorization_def _ hp, padicValNat_factorial (b := Nat.log p n + 2) (by omega)]`. Establish `h1 : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p n + 2)` using `by simp`. Establish `h2` using `Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1`. Simplify using `only [pow_one] at h2`.

Conclude with `h2`.
-/
theorem sz_div_le_fact {p : ℕ} (hp : p.Prime) (n : ℕ) : n / p ≤ (n.factorial).factorization p := by
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat_factorial (b := Nat.log p n + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
  have h2 := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simp only [pow_one] at h2
  exact h2

/- English proof (translation)
Use extensionality with `p`. Simplify using `[Nat.primesLE, Nat.mem_primesBelow]`.
-/
private theorem primesLE_eq_filter_prime_range (n : ℕ) :
    Nat.primesLE n = Finset.filter Nat.Prime (Finset.range (n + 1)) := by
  ext p
  simp [Nat.primesLE, Nat.mem_primesBelow]

/- English proof (translation)
Establish `hsub : Nat.primesLE n ⊆ (n.factorial).factorization.support`. Introduce `p hp`. Rewrite `hp` using `[primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range]`. Rewrite using `[Finsupp.mem_support_iff]`. Conclude with `(hp.2.factorization_pos_of_dvd (Nat.factorial_ne_zero n) (hp.2.dvd_factorial.mpr (by omega))).ne'`.

Rewrite using `[Real.log_nat_eq_sum_factorization, Finsupp.sum]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[primesLE_eq_filter_prime_range, Finset.mem_filter]`.

Apply `mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)` to reduce the goal to its premises. Conclude with `sz_div_le_fact hp.2 n` after adjusting the coercions. Use `_ ≤ ∑ p ∈ (n.factorial).factorization.support, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg hsub` to reduce the goal to its premises. Introduce `p _ _`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`.
-/
theorem sz_sum_div_log (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have hsub : Nat.primesLE n ⊆ (n.factorial).factorization.support := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finsupp.mem_support_iff]
    exact (hp.2.factorization_pos_of_dvd (Nat.factorial_ne_zero n) (hp.2.dvd_factorial.mpr (by omega))).ne'
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
        exact_mod_cast sz_div_le_fact hp.2 n
    _ ≤ ∑ p ∈ (n.factorial).factorization.support, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n` using `by exact_mod_cast Nat.factorial_le_pow n`. Establish `h2 : (0 : ℝ) < (n.factorial : ℕ)` using `by exact_mod_cast Nat.factorial_pos n`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sz_log_fact (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
    _ = n * Real.log n := Real.log_pow n _

/- English proof (translation)
Establish `hn0 : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hprime : ∀ p ∈ Nat.primesLE n, p.Prime`. Introduce `p hp`. Rewrite `hp` using `[primesLE_eq_filter_prime_range, Finset.mem_filter]`. Conclude with `hp.2`.

Establish `htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4`. Establish `h1 : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p`. Rewrite using `[primesLE_eq_filter_prime_range, primorial, Nat.cast_prod, Real.log_prod]`. Introduce `p hp`. Conclude with `(Finset.mem_filter.mp hp).2.ne_zero` after adjusting the coercions.

Rewrite using `[← h1, ← Real.log_pow]`. Apply `Real.log_le_log (by exact_mod_cast primorial_pos n)` to reduce the goal to its premises. Conclude with `primorial_le_4_pow n` after adjusting the coercions. Establish `hfloor : ∀ p ∈ Nat.primesLE n, (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1`. Introduce `p hp`.

Establish `hpp` using `hprime p hp`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hpp.pos`. Rewrite using `[div_le_iff₀ hp0]`. Establish `h1 : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = n` using `by exact_mod_cast Nat.div_add_mod n p`. Establish `h2 : ((n % p : ℕ) : ℝ) < p` using `by exact_mod_cast Nat.mod_lt n hpp.pos`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * Real.log n + n * Real.log 4`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `p _`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ p ∈ Nat.primesLE n, ((((n / p : ℕ) : ℝ) + 1) * Real.log p) := by`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`.

Conclude with `mul_le_mul_of_nonneg_right (hfloor p hp) (Real.log_natCast_nonneg _)`. Use `_ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p := by`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p _`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ n * Real.log n + n * Real.log 4 := by`. Establish `h` using `(sz_sum_div_log n).trans (sz_log_fact n)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left (by rw [mul_add]; exact hmain) hn0`.
-/
theorem sz_mertens (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hprime : ∀ p ∈ Nat.primesLE n, p.Prime := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
    exact hp.2
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    have h1 : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p := by
      rw [primesLE_eq_filter_prime_range, primorial, Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    rw [← h1, ← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast primorial_pos n)
    exact_mod_cast primorial_le_4_pow n
  have hfloor : ∀ p ∈ Nat.primesLE n, (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
    intro p hp
    have hpp := hprime p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [div_le_iff₀ hp0]
    have h1 : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = n := by exact_mod_cast Nat.div_add_mod n p
    have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hpp.pos
    nlinarith
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * Real.log n + n * Real.log 4 := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
        = ∑ p ∈ Nat.primesLE n, (n : ℝ) / p * Real.log p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ ∑ p ∈ Nat.primesLE n, ((((n / p : ℕ) : ℝ) + 1) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_right (hfloor p hp) (Real.log_natCast_nonneg _)
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ n * Real.log n + n * Real.log 4 := by
          have h := (sz_sum_div_log n).trans (sz_log_fact n)
          linarith
  exact le_of_mul_le_mul_left (by rw [mul_add]; exact hmain) hn0

/- English proof (translation)
Unfold `lpF`. Establish `h : 0 ≤ sSup (lpFeasible l d Ds)`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `y ⟨xs, h0, -, -, rfl⟩`. Conclude with `Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sz_lpF_le (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) :
    lpF l d Ds ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ s, Ds s := by
  unfold lpF
  have h : 0 ≤ sSup (lpFeasible l d Ds) := by
    apply Real.sSup_nonneg
    rintro y ⟨xs, h0, -, -, rfl⟩
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
  linarith

/- English proof (translation)
Unfold `kindA`. Simplify using `only [hns, not_false_eq_true, true_and]`. Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`. Simplify using the standard rewrite rules.
-/
theorem sz_sum_kindA {D : D7} {p : ℕ} (hns : ¬ IsSg D p) (f : Bool × HH D → ℝ) :
    ∑ z ∈ kindA D p, f z = ∑ t : HH D, f (false, t) := by
  unfold kindA
  simp only [hns, not_false_eq_true, true_and]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

/- English proof (translation)
Simplify using `[posPl, partner, hns]`.
-/
theorem sz_posPl {D : D7} {p : ℕ} (hns : ¬ IsSg D p) (t : HH D) (e : ℕ) :
    posPl D p (false, t) e = (false, t + e • hP D p) := by
  simp [posPl, partner, hns]

/- English proof (translation)
Establish `hnz : (nP D p : ℝ) ≠ 0` using `by exact_mod_cast NeZero.ne (nP D p)`. Establish `hshift : ∀ c : HH D, ∑ t : HH D, wPl D j (false, t + c) = ∑ t : HH D, wPl D j (false, t)` using `fun c => Equiv.sum_comp (Equiv.addRight c) (fun t => wPl D j (false, t))`. Establish `hsum : ∑ t : HH D, FOrb D j p (false, t) ≤ ∑ t : HH D, (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s : ZMod (nP D p), (((D.R.k : ℝ) - 1) * wPl D j (false, t + s.val • hP D p))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t _`.

Establish `h` using `sz_lpF_le p (nP D p) (fun s : ZMod (nP D p) => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p (false, t) s.val))`. Simplify using `only [sz_posPl hns] at h`. Unfold `FOrb`. Simplify using `only [sz_posPl hns]`. Conclude with `h`.

Establish `heq : ∑ t : HH D, (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ∑ s : ZMod (nP D p), (((D.R.k : ℝ) - 1) * wPl D j (false, t + s.val • hP D p)) = (p : ℝ) / ((p : ℝ) ^ 2 - 1) * (((D.R.k : ℝ) - 1) * ∑ t : HH D, wPl D j (false, t)) * (nP D p : ℝ)`. Rewrite using `[← Finset.mul_sum, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, hshift]`. Rewrite using `[Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `FkindA`. Rewrite using `[sz_sum_kindA hns, div_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hnz))]`. Conclude with `hsum.trans heq.le`.
-/
theorem sz_FkindA_le {D : D7} (j p : ℕ) (hns : ¬ IsSg D p) :
    FkindA D j p ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * (((D.R.k : ℝ) - 1) * ∑ t : HH D, wPl D j (false, t)) := by
  have hnz : (nP D p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (nP D p)
  have hshift : ∀ c : HH D, ∑ t : HH D, wPl D j (false, t + c) = ∑ t : HH D, wPl D j (false, t) :=
    fun c => Equiv.sum_comp (Equiv.addRight c) (fun t => wPl D j (false, t))
  have hsum : ∑ t : HH D, FOrb D j p (false, t) ≤ ∑ t : HH D, (p : ℝ) / ((p : ℝ) ^ 2 - 1) *
      ∑ s : ZMod (nP D p), (((D.R.k : ℝ) - 1) * wPl D j (false, t + s.val • hP D p)) := by
    apply Finset.sum_le_sum
    intro t _
    have h := sz_lpF_le p (nP D p)
      (fun s : ZMod (nP D p) => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p (false, t) s.val))
    simp only [sz_posPl hns] at h
    unfold FOrb
    simp only [sz_posPl hns]
    exact h
  have heq : ∑ t : HH D, (p : ℝ) / ((p : ℝ) ^ 2 - 1) *
      ∑ s : ZMod (nP D p), (((D.R.k : ℝ) - 1) * wPl D j (false, t + s.val • hP D p)) =
      (p : ℝ) / ((p : ℝ) ^ 2 - 1) * (((D.R.k : ℝ) - 1) * ∑ t : HH D, wPl D j (false, t)) * (nP D p : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hshift]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    ring
  unfold FkindA
  rw [sz_sum_kindA hns, div_le_iff₀ (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hnz))]
  exact hsum.trans heq.le

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card]`. Use `show Nat.card (Fin D.R.ord) = D.R.ord`. Simplify using the standard rewrite rules.
-/
private theorem card_HH_eq_n (D : D7) : Fintype.card (HH D) = D.R.n := by
  rw [← Nat.card_eq_fintype_card]
  show Nat.card (Fin D.R.ord) = D.R.ord
  simp

/- English proof (translation)
Establish `h1 : ∀ t : HH D, wPl D j (false, t) ≤ (if t ∈ D.host.TT then 2 * L.sc.b' else 0) + 2 * L.sc.w'' D.R.n`. Introduce `t`. Establish `h` using `hK j hj t`. Use `split_ifs at h ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.sum_const, Finset.card_univ, card_HH_eq_n]`. Simplify using `only [nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sz_sumW {D : D7} {L : SizeData₂ D} (hK : KindA D L) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (hw : 0 ≤ L.sc.w'' D.R.n) :
    ∑ t : HH D, wPl D j (false, t) ≤
      2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n := by
  have h1 : ∀ t : HH D, wPl D j (false, t) ≤
      (if t ∈ D.host.TT then 2 * L.sc.b' else 0) + 2 * L.sc.w'' D.R.n := by
    intro t
    have h := hK j hj t
    split_ifs at h ⊢
    · linarith
    · linarith
  calc ∑ t : HH D, wPl D j (false, t)
      ≤ ∑ t : HH D, ((if t ∈ D.host.TT then 2 * L.sc.b' else 0) + 2 * L.sc.w'' D.R.n) :=
        Finset.sum_le_sum fun t _ => h1 t
    _ = 2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, card_HH_eq_n]
        simp only [nsmul_eq_mul]
        ring

/- English proof (translation)
Unfold `Scale.b' Scale.a Scale.b Scale.X'`. Conclude with `div_pos (mul_pos (by linarith [s.one_lt_alt]) (Real.exp_pos _)) (Real.exp_pos _)`.
-/
theorem sz_b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.a Scale.b Scale.X'
  exact div_pos (mul_pos (by linarith [s.one_lt_alt]) (Real.exp_pos _)) (Real.exp_pos _)

/- English proof (translation)
Unfold `Ranks.n`. Establish `h1` using `R.two_le_m`. Establish `h2` using `R.m_le_f`. Use linear arithmetic over natural numbers and integers.
-/
theorem sz_n_pos (R : Ranks) : 0 < R.n := by
  unfold Ranks.n
  have h1 := R.two_le_m
  have h2 := R.m_le_f
  omega

/- English proof (translation)
Unfold `Scale.w''`. Establish `hn : (0 : ℝ) < R.n` using `by exact_mod_cast sz_n_pos R`. Conclude with `div_pos (sz_b'_pos s) (mul_pos (by linarith [s.one_lt_alt]) hn)`.
-/
theorem sz_w''_pos (s : Scale) (R : Ranks) : 0 < s.w'' R.n := by
  unfold Scale.w''
  have hn : (0 : ℝ) < R.n := by exact_mod_cast sz_n_pos R
  exact div_pos (sz_b'_pos s) (mul_pos (by linarith [s.one_lt_alt]) hn)

/- English proof (translation)
Establish `hx : 0 < s.x` using `by linarith [s.one_lt_alt]`. Establish `ha : 0 < s.a`. Unfold `Scale.a Scale.b`. Conclude with `mul_pos hx (Real.exp_pos _)`. Establish `hX : 0 < s.X'`.

Unfold `Scale.X'`. Conclude with `Real.exp_pos _`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Unfold `Scale.X'' Scale.w'' Scale.b'`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`.
-/
theorem sz_X'' (s : Scale) (n : ℕ) (hn : 0 < n) : s.X'' n = s.x * n * s.X' := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have ha : 0 < s.a := by
    unfold Scale.a Scale.b
    exact mul_pos hx (Real.exp_pos _)
  have hX : 0 < s.X' := by
    unfold Scale.X'
    exact Real.exp_pos _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Scale.X'' Scale.w'' Scale.b'
  field_simp
  try ring

/- English proof (translation)
Establish `hn` using `sz_n_pos R`. Rewrite using `[sz_X'' s R.n hn]`. Establish `hx` using `s.one_lt_alt`. Establish `hn1 : (1 : ℝ) ≤ R.n` using `by exact_mod_cast hn`. Establish `hX : Real.exp 1 ≤ s.X'`.

Unfold `Scale.X'`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Conclude with `Real.one_le_rpow hx.le (by linarith [s.eps_pos])`. Establish `h1 : 1 ≤ s.x * R.n` using `by nlinarith`. Establish `hX0 : 0 < s.X'` using `lt_of_lt_of_le (Real.exp_pos 1) hX`.

Establish `h2` using `mul_le_mul_of_nonneg_right h1 hX0.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sz_X''_ge (s : Scale) (R : Ranks) : Real.exp 1 ≤ s.X'' R.n := by
  have hn := sz_n_pos R
  rw [sz_X'' s R.n hn]
  have hx := s.one_lt_alt
  have hn1 : (1 : ℝ) ≤ R.n := by exact_mod_cast hn
  have hX : Real.exp 1 ≤ s.X' := by
    unfold Scale.X'
    apply Real.exp_le_exp.mpr
    exact Real.one_le_rpow hx.le (by linarith [s.eps_pos])
  have h1 : 1 ≤ s.x * R.n := by nlinarith
  have hX0 : 0 < s.X' := lt_of_lt_of_le (Real.exp_pos 1) hX
  have h2 := mul_le_mul_of_nonneg_right h1 hX0.le
  linarith

/- English proof (translation)
Introduce `_hS hK j hj`. Establish `hn` using `sz_n_pos D.R`. Establish `hnR : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast hn`. Establish `hb` using `sz_b'_pos L.sc`. Establish `hw` using `sz_w''_pos L.sc D.R`.

Establish `hx` using `L.sc.one_lt_alt`. Establish `hk : (1 : ℝ) ≤ D.R.k`. Establish `h1` using `D.R.m_add_three_le_k`. Establish `h2` using `D.R.two_le_m`. Conclude with `(by omega : 1 ≤ D.R.k)` after adjusting the coercions.

Establish `hk0 : (0 : ℝ) ≤ D.R.k` using `by linarith`. Establish `hTT : (D.host.TT.card : ℝ) ≤ D.R.n`. Rewrite using `[← card_HH_eq_n D]`. Conclude with `Finset.card_le_univ _` after adjusting the coercions. Establish `hw'' : L.sc.w'' D.R.n ≤ L.sc.b'`.

Unfold `Scale.w''`. Conclude with `div_le_self hb.le (by nlinarith)`. Establish `hB0 : 0 ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n` using `by positivity`. Establish `hB4 : 2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n ≤ 4 * D.R.n * L.sc.b'`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hTT hb.le, mul_le_mul_of_nonneg_left hw'' (by linarith : (0 : ℝ) ≤ D.R.n)]`.

Establish `hpart : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → hP D p ≠ 0 → max 0 (FkindA D j p) ≤ 2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ∧ 2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ≤ …`. Introduce `p hp hC _`. Establish `hns : ¬ IsSg D p`. Unfold `IsSg`. Rewrite using `[hC]`.

Simplify using the standard rewrite rules. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hF` using `sz_FkindA_le j p hns`. Establish `hW` using `sz_sumW hK j hj hw.le`.

Establish `hγ0 : 0 ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1)` using `div_nonneg hp0.le (by nlinarith)`. Establish `hγ : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 2 / p`. Rewrite using `[div_le_div_iff₀ (by nlinarith) hp0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hk1 : 0 ≤ (D.R.k : ℝ) - 1` using `by linarith`.

Prove the components needed by the constructor for the conclusion. Apply `max_le` to reduce the goal to its premises. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Use `⟨hpart, ?_⟩` and prove the remaining obligations. Introduce `S hS`. Establish `hX` using `sz_X''_ge L.sc D.R`. Establish `hX0 : 0 < L.sc.X'' D.R.n` using `lt_of_lt_of_le (Real.exp_pos 1) hX`. Establish `hlogX : 1 ≤ Real.log (L.sc.X'' D.R.n)`.

Establish `h` using `Real.log_le_log (Real.exp_pos 1) hX`. Rewrite `h` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hN1 : 1 ≤ ⌊L.sc.X'' D.R.n⌋₊`. Apply `Nat.le_floor` to reduce the goal to its premises. Establish `h` using `Real.add_one_le_exp 1`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hNle : (⌊L.sc.X'' D.R.n⌋₊ : ℝ) ≤ L.sc.X'' D.R.n` using `Nat.floor_le hX0.le`. Establish `hsub : S ⊆ Nat.primesLE ⌊L.sc.X'' D.R.n⌋₊`. Introduce `p hp`.

Take `⟨hpp, -, -, hpX⟩` from `hS p hp`. Rewrite using `[primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range]`. Conclude with `⟨Nat.lt_succ_of_le (Nat.le_floor hpX), hpp⟩`. Establish `hM` using `sz_mertens ⌊L.sc.X'' D.R.n⌋₊ hN1`. Establish `hlogN : Real.log (⌊L.sc.X'' D.R.n⌋₊ : ℝ) ≤ Real.log (L.sc.X'' D.R.n)` using `Real.log_le_log (by exact_mod_cast hN1) hNle`.

Establish `hlog4 : Real.log 4 ≤ 2 * Real.log (L.sc.X'' D.R.n)`. Establish `h4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]`. Evaluate the numerical expressions. Establish `h2` using `Real.log_two_lt_d9`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSsum : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊L.sc.X'' D.R.n⌋₊, Real.log p / p`. Apply `Finset.sum_le_sum_of_subset_of_nonneg hsub` to reduce the goal to its premises. Introduce `p _ _`. Conclude with `div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)`.

Establish `hK8 : 0 ≤ 8 * (D.R.k : ℝ) * D.R.n * L.sc.b'` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Take `⟨hpp, hC, hh, -⟩` from `hS p hp`.

Establish `h` using `hpart p hpp hC hh`. Conclude with `mul_le_mul_of_nonneg_left (h.1.trans h.2) (Real.log_natCast_nonneg _)`. Use `_ = 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' * ∑ p ∈ S, Real.log p / p := by`. Rewrite using `[Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `p _`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' * (3 * Real.log (L.sc.X'' D.R.n)) := by`. Apply `mul_le_mul_of_nonneg_left _ hK8` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Use `_ = 12 * (D.R.k : ℝ) * D.R.f * L.sc.b' * Real.log (L.sc.X'' D.R.n) := by`. Unfold `Ranks.f`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem first_term_size_bound (D : D7) (L : SizeData₂ D) : ErrorFirstTermSize D L 12 := by
  intro _hS hK j hj
  have hn := sz_n_pos D.R
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hb := sz_b'_pos L.sc
  have hw := sz_w''_pos L.sc D.R
  have hx := L.sc.one_lt_alt
  have hk : (1 : ℝ) ≤ D.R.k := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hk0 : (0 : ℝ) ≤ D.R.k := by linarith
  have hTT : (D.host.TT.card : ℝ) ≤ D.R.n := by
    rw [← card_HH_eq_n D]
    exact_mod_cast Finset.card_le_univ _
  have hw'' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    unfold Scale.w''
    exact div_le_self hb.le (by nlinarith)
  have hB0 : 0 ≤ 2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n := by positivity
  have hB4 : 2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n ≤
      4 * D.R.n * L.sc.b' := by
    nlinarith [mul_le_mul_of_nonneg_right hTT hb.le,
      mul_le_mul_of_nonneg_left hw'' (by linarith : (0 : ℝ) ≤ D.R.n)]
  have hpart : ∀ p : ℕ, p.Prime → IsResidueClassZero D p → hP D p ≠ 0 →
      max 0 (FkindA D j p) ≤
        2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ∧
      2 * (D.R.k : ℝ) / p * (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) ≤
        8 * (D.R.k : ℝ) * D.R.n * L.sc.b' / p := by
    intro p hp hC _
    have hns : ¬ IsSg D p := by
      unfold IsSg
      rw [hC]
      simp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hF := sz_FkindA_le j p hns
    have hW := sz_sumW hK j hj hw.le
    have hγ0 : 0 ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) := div_nonneg hp0.le (by nlinarith)
    have hγ : (p : ℝ) / ((p : ℝ) ^ 2 - 1) ≤ 2 / p := by
      rw [div_le_div_iff₀ (by nlinarith) hp0]
      nlinarith
    have hk1 : 0 ≤ (D.R.k : ℝ) - 1 := by linarith
    constructor
    · apply max_le
      · positivity
      · calc FkindA D j p
            ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * (((D.R.k : ℝ) - 1) * ∑ t : HH D, wPl D j (false, t)) := hF
          _ ≤ (p : ℝ) / ((p : ℝ) ^ 2 - 1) * (((D.R.k : ℝ) - 1) *
              (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hk1) hγ0
          _ ≤ 2 / p * ((D.R.k : ℝ) *
              (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n)) :=
            mul_le_mul hγ (by nlinarith) (mul_nonneg hk1 hB0) (by positivity)
          _ = 2 * (D.R.k : ℝ) / p *
              (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n) := by ring
    · calc 2 * (D.R.k : ℝ) / p *
            (2 * (D.host.TT.card : ℝ) * L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.w'' D.R.n)
          ≤ 2 * (D.R.k : ℝ) / p * (4 * D.R.n * L.sc.b') :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
        _ = 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' / p := by ring
  refine ⟨hpart, ?_⟩
  intro S hS
  have hX := sz_X''_ge L.sc D.R
  have hX0 : 0 < L.sc.X'' D.R.n := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX : 1 ≤ Real.log (L.sc.X'' D.R.n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hN1 : 1 ≤ ⌊L.sc.X'' D.R.n⌋₊ := by
    apply Nat.le_floor
    have h := Real.add_one_le_exp 1
    push_cast
    linarith
  have hNle : (⌊L.sc.X'' D.R.n⌋₊ : ℝ) ≤ L.sc.X'' D.R.n := Nat.floor_le hX0.le
  have hsub : S ⊆ Nat.primesLE ⌊L.sc.X'' D.R.n⌋₊ := by
    intro p hp
    obtain ⟨hpp, -, -, hpX⟩ := hS p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpX), hpp⟩
  have hM := sz_mertens ⌊L.sc.X'' D.R.n⌋₊ hN1
  have hlogN : Real.log (⌊L.sc.X'' D.R.n⌋₊ : ℝ) ≤ Real.log (L.sc.X'' D.R.n) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlog4 : Real.log 4 ≤ 2 * Real.log (L.sc.X'' D.R.n) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_lt_d9
    linarith
  have hSsum : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ Nat.primesLE ⌊L.sc.X'' D.R.n⌋₊, Real.log p / p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hK8 : 0 ≤ 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' := by positivity
  calc ∑ p ∈ S, Real.log p * max 0 (FkindA D j p)
      ≤ ∑ p ∈ S, Real.log p * (8 * (D.R.k : ℝ) * D.R.n * L.sc.b' / p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpp, hC, hh, -⟩ := hS p hp
        have h := hpart p hpp hC hh
        exact mul_le_mul_of_nonneg_left (h.1.trans h.2) (Real.log_natCast_nonneg _)
    _ = 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' * ∑ p ∈ S, Real.log p / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ 8 * (D.R.k : ℝ) * D.R.n * L.sc.b' * (3 * Real.log (L.sc.X'' D.R.n)) := by
        apply mul_le_mul_of_nonneg_left _ hK8
        linarith
    _ = 12 * (D.R.k : ℝ) * D.R.f * L.sc.b' * Real.log (L.sc.X'' D.R.n) := by
        unfold Ranks.f
        push_cast
        ring

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
