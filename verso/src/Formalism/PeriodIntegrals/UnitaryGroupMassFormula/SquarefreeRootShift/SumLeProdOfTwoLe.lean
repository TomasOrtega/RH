import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.Development

open Finset

noncomputable section

namespace PI.SqfRootShift.W

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[sum_insert ha, prod_insert ha]`. Establish `h2 : 2 ≤ f a` using `hf a (mem_insert_self a s)`.

Establish `hs : ∀ i ∈ s, 2 ≤ f i` using `fun i hi => hf i (mem_insert_of_mem hi)`. Establish `ih'` using `ih hs`. Establish `hP : 0 < ∏ i ∈ s, f i` using `prod_pos (fun i hi => by have := hs i hi; omega)`. Break down `s.eq_empty_or_nonempty with he | ⟨b, hb⟩` into its components or cases. Substitute `he` using the available equality.

Simplify using the standard rewrite rules. Establish `hb2 : 2 ≤ ∏ i ∈ s, f i` using `(hs b hb).trans (Nat.le_of_dvd hP (dvd_prod_of_mem f hb))`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, 2 ≤ f i) :
    ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have h2 : 2 ≤ f a := hf a (mem_insert_self a s)
    have hs : ∀ i ∈ s, 2 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have ih' := ih hs
    have hP : 0 < ∏ i ∈ s, f i := prod_pos (fun i hi => by have := hs i hi; omega)
    rcases s.eq_empty_or_nonempty with he | ⟨b, hb⟩
    · subst he; simp
    · have hb2 : 2 ≤ ∏ i ∈ s, f i :=
        (hs b hb).trans (Nat.le_of_dvd hP (dvd_prod_of_mem f hb))
      nlinarith

/- English proof (translation)
Establish `hpp` using `Nat.prime_of_mem_primeFactors hp`. Establish `hpos : 0 < N.factorization p`. Rewrite `hp` using `[Nat.mem_primeFactors]`. Conclude with `hpp.factorization_pos_of_dvd hp.2.2 hp.2.1`. Conclude with `Nat.le_self_pow hpos.ne' p`.
-/
theorem le_pp {N p : ℕ} (hp : p ∈ N.primeFactors) : p ≤ p ^ N.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < N.factorization p := by
    rw [Nat.mem_primeFactors] at hp
    exact hpp.factorization_pos_of_dvd hp.2.2 hp.2.1
  exact Nat.le_self_pow hpos.ne' p

/- English proof (translation)
The claim follows from `(Nat.prime_of_mem_primeFactors hp).two_le.trans (le_pp hp)`.
-/
theorem two_le_pp {N p : ℕ} (hp : p ∈ N.primeFactors) : 2 ≤ p ^ N.factorization p :=
  (Nat.prime_of_mem_primeFactors hp).two_le.trans (le_pp hp)

/- English proof (translation)
Use `Nat.prod_factorization_pow_eq_self hN` as an intermediate fact. Rewrite `this` using `[Finsupp.prod, Nat.support_factorization]`. Then use the resulting hypothesis.
-/
theorem prod_pp {N : ℕ} (hN : N ≠ 0) : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
  have := Nat.prod_factorization_pow_eq_self hN
  rwa [Finsupp.prod, Nat.support_factorization] at this

/- English proof (translation)
Unfold `ppSum`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ppSum_le_self {N : ℕ} (hN : N ≠ 0) : ppSum N ≤ N := by
  unfold ppSum
  calc _ ≤ ∏ p ∈ N.primeFactors, p ^ N.factorization p :=
        sum_le_prod_of_two_le _ _ (fun p hp => two_le_pp hp)
    _ = N := prod_pp hN

/- English proof (translation)
Establish `h2mem : 2 ∈ n.primeFactors` using `Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (by norm_num : 2 ∣ 16).trans h16, hn⟩`. Establish `hqmem : q ∈ n.primeFactors` using `Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩`. Establish `hdmem : d ∈ n.primeFactors` using `Nat.mem_primeFactors.mpr ⟨hd, hdn, hn⟩`. Establish `hq1 : q ∈ n.primeFactors.erase 2` using `Finset.mem_erase.mpr ⟨by omega, hqmem⟩`. Establish `hd1 : d ∈ (n.primeFactors.erase 2).erase q` using `Finset.mem_erase.mpr ⟨Ne.symm hqd, Finset.mem_erase.mpr ⟨by omega, hdmem⟩⟩`.

Establish `hsub : ((n.primeFactors.erase 2).erase q).erase d ⊆ n.primeFactors` using `fun p hp => by`. Simplify using `only [Finset.mem_erase] at hp`. Conclude with `hp.2.2.2`. Establish `hsum : ppSum n = 2 ^ n.factorization 2 + (q ^ n.factorization q + (d ^ n.factorization d + ∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p))`. Unfold `ppSum`.

Rewrite using `[← Finset.add_sum_erase _ _ h2mem, ← Finset.add_sum_erase _ _ hq1, ← Finset.add_sum_erase _ _ hd1]`. Establish `hprod : n = 2 ^ n.factorization 2 * (q ^ n.factorization q * (d ^ n.factorization d * ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p))`. Establish `h0` using `prod_pp hn`. Rewrite `h0` using `[← Finset.mul_prod_erase _ _ h2mem, ← Finset.mul_prod_erase _ _ hq1, ← Finset.mul_prod_erase _ _ hd1]`. Conclude with `h0.symm`.

Establish `hR` using `sum_le_prod_of_two_le (((n.primeFactors.erase 2).erase q).erase d) (fun p => p ^ n.factorization p) (fun p hp => two_le_pp (hsub hp))`. Establish `hPi : 0 < ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p` using `prod_pos (fun p hp => by have := two_le_pp (hsub hp); omega)`. Establish `hA : 16 ≤ 2 ^ n.factorization 2`. Establish `h4 : 4 ≤ n.factorization 2` using `(Nat.prime_two.pow_dvd_iff_le_factorization hn).mp (by simpa using h16)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hB : q ≤ q ^ n.factorization q` using `le_pp hqmem`. Establish `hC : d ≤ d ^ n.factorization d` using `le_pp hdmem`. Establish `hm1 : min q d ≤ q` using `min_le_left _ _`. Establish `hm2 : min q d ≤ d` using `min_le_right _ _`. Rewrite using `[hsum]`.

Generalize the expression as in `2 ^ n.factorization 2 = A at hprod hA ⊢`. Generalize the expression as in `q ^ n.factorization q = B at hprod hB ⊢`. Generalize the expression as in `d ^ n.factorization d = C at hprod hC ⊢`. Generalize the expression as in `∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = R at hR ⊢`. Generalize the expression as in `∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = P at hprod hR hPi ⊢`.

Generalize the expression as in `min q d = m at hm1 hm2 ⊢`. Substitute `hprod` using the available equality. Establish `e1 : 16 * (m * A) ≤ A * (B * (C * P))`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : 16 * (m * B) ≤ A * (B * (C * P))`.

Combine the equalities or inequalities in the displayed calculation. Establish `e3 : 16 * (m * C) ≤ A * (B * (C * P))`. Combine the equalities or inequalities in the displayed calculation. Establish `e4 : 16 * (4 * (m * R)) ≤ A * (B * (C * P))`. Combine the equalities or inequalities in the displayed calculation.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem arith1 {n q d : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hd : d.Prime) (hqd : q ≠ d)
    (hq16 : 16 ≤ q) (hd16 : 16 ≤ d) (h16 : 16 ∣ n) (hqn : q ∣ n) (hdn : d ∣ n) :
    4 * min q d * ppSum n ≤ n := by
  classical
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, (by norm_num : 2 ∣ 16).trans h16, hn⟩
  have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
  have hdmem : d ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdn, hn⟩
  have hq1 : q ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by omega, hqmem⟩
  have hd1 : d ∈ (n.primeFactors.erase 2).erase q :=
    Finset.mem_erase.mpr ⟨Ne.symm hqd, Finset.mem_erase.mpr ⟨by omega, hdmem⟩⟩
  have hsub : ((n.primeFactors.erase 2).erase q).erase d ⊆ n.primeFactors := fun p hp => by
    simp only [Finset.mem_erase] at hp; exact hp.2.2.2
  have hsum : ppSum n = 2 ^ n.factorization 2 + (q ^ n.factorization q + (d ^ n.factorization d +
      ∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p)) := by
    unfold ppSum
    rw [← Finset.add_sum_erase _ _ h2mem, ← Finset.add_sum_erase _ _ hq1,
      ← Finset.add_sum_erase _ _ hd1]
  have hprod : n = 2 ^ n.factorization 2 * (q ^ n.factorization q * (d ^ n.factorization d *
      ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p)) := by
    have h0 := prod_pp hn
    rw [← Finset.mul_prod_erase _ _ h2mem, ← Finset.mul_prod_erase _ _ hq1,
      ← Finset.mul_prod_erase _ _ hd1] at h0
    exact h0.symm
  have hR := sum_le_prod_of_two_le (((n.primeFactors.erase 2).erase q).erase d)
    (fun p => p ^ n.factorization p) (fun p hp => two_le_pp (hsub hp))
  have hPi : 0 < ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p :=
    prod_pos (fun p hp => by have := two_le_pp (hsub hp); omega)
  have hA : 16 ≤ 2 ^ n.factorization 2 := by
    have h4 : 4 ≤ n.factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp (by simpa using h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) h4
  have hB : q ≤ q ^ n.factorization q := le_pp hqmem
  have hC : d ≤ d ^ n.factorization d := le_pp hdmem
  have hm1 : min q d ≤ q := min_le_left _ _
  have hm2 : min q d ≤ d := min_le_right _ _
  rw [hsum]
  generalize 2 ^ n.factorization 2 = A at hprod hA ⊢
  generalize q ^ n.factorization q = B at hprod hB ⊢
  generalize d ^ n.factorization d = C at hprod hC ⊢
  generalize ∑ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = R at hR ⊢
  generalize ∏ p ∈ ((n.primeFactors.erase 2).erase q).erase d, p ^ n.factorization p = P
    at hprod hR hPi ⊢
  generalize min q d = m at hm1 hm2 ⊢
  subst hprod
  have e1 : 16 * (m * A) ≤ A * (B * (C * P)) := by
    calc 16 * (m * A) ≤ C * (B * A) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e2 : 16 * (m * B) ≤ A * (B * (C * P)) := by
    calc 16 * (m * B) ≤ A * (C * B) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e3 : 16 * (m * C) ≤ A * (B * (C * P)) := by
    calc 16 * (m * C) ≤ A * (B * C) := Nat.mul_le_mul hA (Nat.mul_le_mul_right _ (by omega))
      _ = A * (B * (C * 1)) := by ring
      _ ≤ A * (B * (C * P)) := by gcongr; omega
  have e4 : 16 * (4 * (m * R)) ≤ A * (B * (C * P)) := by
    calc 16 * (4 * (m * R)) ≤ A * (C * (B * P)) :=
          Nat.mul_le_mul hA (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) hR))
      _ = A * (B * (C * P)) := by ring
  nlinarith

/- English proof (translation)
Establish `hgk : 2 ≤ g ^ k` using `le_trans hg (Nat.le_self_pow hk g)`. Establish `hne1 : g ^ k - 1 ≠ 0` using `by omega`. Establish `hne2 : g - 1 ≠ 0` using `by omega`. Establish `h4' : (4 : ℤ) ∣ (g : ℤ) - 1`. Take `⟨t, ht⟩` from `h4`.

Conclude with `⟨(t : ℤ), by omega⟩`. Establish `hx : ¬ (2 : ℤ) ∣ (g : ℤ)`. Establish `: ¬ 2 ∣ g` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `key` using `Int.two_pow_sub_pow' k h4' hx`.

Rewrite `key` using `[one_pow]`. Establish `e1 : ((g : ℤ) ^ k - 1) = ((g ^ k - 1 : ℕ) : ℤ)`. Move the coercions through the operations in `[Nat.cast_sub (by omega : 1 ≤ g ^ k)]; ring`. Establish `e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ)`. Move the coercions through the operations in `[Nat.cast_sub (by omega : 1 ≤ g)]; ring`.

Establish `e3 : (2 : ℤ) = ((2 : ℕ) : ℤ)` using `by norm_num`. Rewrite `key` using `[e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity, Int.natCast_emultiplicity]`. Rewrite using `[← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hne1, padicValNat_eq_emultiplicity hne2, padicValNat_eq_emultiplicity hk]`. Conclude with `key`.
-/
theorem lte_two {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    padicValNat 2 (g ^ k - 1) = padicValNat 2 (g - 1) + padicValNat 2 k := by
  have hgk : 2 ≤ g ^ k := le_trans hg (Nat.le_self_pow hk g)
  have hne1 : g ^ k - 1 ≠ 0 := by omega
  have hne2 : g - 1 ≠ 0 := by omega
  have h4' : (4 : ℤ) ∣ (g : ℤ) - 1 := by
    obtain ⟨t, ht⟩ := h4
    exact ⟨(t : ℤ), by omega⟩
  have hx : ¬ (2 : ℤ) ∣ (g : ℤ) := by
    have : ¬ 2 ∣ g := by omega
    exact_mod_cast this
  have key := Int.two_pow_sub_pow' k h4' hx
  rw [one_pow] at key
  have e1 : ((g : ℤ) ^ k - 1) = ((g ^ k - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g ^ k)]; ring
  have e2 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)]; ring
  have e3 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
  rw [e1, e2, e3, Int.natCast_emultiplicity, Int.natCast_emultiplicity,
    Int.natCast_emultiplicity] at key
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, padicValNat_eq_emultiplicity hne1,
    padicValNat_eq_emultiplicity hne2, padicValNat_eq_emultiplicity hk]
  exact key

/- English proof (translation)
Establish `hx : ¬ p ∣ g`. Introduce `h`. Establish `h1 : p ∣ g - 1 + 1` using `by rwa [show g - 1 + 1 = g by omega]`. Establish `h2 : p ∣ 1` using `(Nat.dvd_add_right hpg).mp h1`. Conclude with `(Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)`.

Use `padicValNat.pow_sub_pow (p := p) (x := g) (y := 1) hp (by omega) (by simpa using hpg) hx hk` as an intermediate fact. Simplify using `using this`.
-/
theorem lte_odd {p g k : ℕ} [Fact p.Prime] (hp : Odd p) (hg : 2 ≤ g) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k := by
  have hx : ¬ p ∣ g := by
    intro h
    have h1 : p ∣ g - 1 + 1 := by rwa [show g - 1 + 1 = g by omega]
    have h2 : p ∣ 1 := (Nat.dvd_add_right hpg).mp h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  have := padicValNat.pow_sub_pow (p := p) (x := g) (y := 1) hp (by omega) (by simpa using hpg)
    hx hk
  simpa using this

/- English proof (translation)
Use `Fact.mk hp` as an intermediate fact. Establish `hv : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k`. Break down `hp.eq_two_or_odd' with rfl | hodd` into its components or cases. Conclude with `lte_two hg h4 hk`. Conclude with `lte_odd hodd hg hpg hk`.

Rewrite using `[Nat.factorization_def _ hp, Nat.factorization_def _ hp, hv, pow_add, mul_comm k]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) pow_padicValNat_dvd)`.
-/
theorem pp_lte {p g k : ℕ} (hp : p.Prime) (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hpg : p ∣ g - 1)
    (hk : k ≠ 0) : p ^ (g ^ k - 1).factorization p ≤ k * p ^ (g - 1).factorization p := by
  have := Fact.mk hp
  have hv : padicValNat p (g ^ k - 1) = padicValNat p (g - 1) + padicValNat p k := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact lte_two hg h4 hk
    · exact lte_odd hodd hg hpg hk
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, hv, pow_add, mul_comm k]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) pow_padicValNat_dvd)

/- English proof (translation)
Establish `hdvd : g - 1 ∣ g ^ k - 1` using `by simpa using Nat.sub_dvd_pow_sub_pow g 1 k`. Establish `hgk : 2 ≤ g ^ k` using `le_trans hg (Nat.le_self_pow hk g)`. Establish `hN0 : g ^ k - 1 ≠ 0` using `by omega`. Establish `hg0 : g - 1 ≠ 0` using `by omega`. Establish `hNS : g ^ k - 1 = (g - 1) * ((g ^ k - 1) / (g - 1))` using `(Nat.mul_div_cancel' hdvd).symm`.

Establish `hS0 : (g ^ k - 1) / (g - 1) ≠ 0`. Introduce `h`. Rewrite `hNS` using `[h, mul_zero]`. Conclude with `hN0 hNS`. Unfold `ppSum`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not (g ^ k - 1).primeFactors (fun p => p ∣ g - 1)]`. Use `add_le_add ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter, Nat.mem_primeFactors]`. Conclude with `pp_lte hp.1.1 hg h4 hp.2 hk`. Use `_ ≤ ∑ p ∈ (g - 1).primeFactors, k * p ^ (g - 1).factorization p := by`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter, Nat.mem_primeFactors]`. Rewrite using `[Nat.mem_primeFactors]`. Conclude with `⟨hp.1.1, hp.2, hg0⟩`. Use `_ = k * ∑ p ∈ (g - 1).primeFactors, p ^ (g - 1).factorization p := by rw [Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Use `conv_lhs => rw [hNS]`. Rewrite using `[Nat.factorization_mul hg0 hS0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hp.2, zero_add]`.

Use `_ ≤ ∑ p ∈ ((g ^ k - 1) / (g - 1)).primeFactors, p ^ ((g ^ k - 1) / (g - 1)).factorization p := by`. Apply `Finset.sum_le_sum_of_subset` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter, Nat.mem_primeFactors]`. Rewrite using `[Nat.mem_primeFactors]`.

Use `⟨hp.1.1, ?_, hS0⟩` and prove the remaining obligations. Establish `h1 : p ∣ (g - 1) * ((g ^ k - 1) / (g - 1))` using `hNS ▸ hp.1.2.1`. Conclude with `(hp.1.1.dvd_mul.mp h1).resolve_left hp.2`. Use `_ ≤ (g ^ k - 1) / (g - 1) := ppSum_le_self hS0`.
-/
theorem arith2 {g k : ℕ} (hg : 2 ≤ g) (h4 : 4 ∣ g - 1) (hk : k ≠ 0) :
    ppSum (g ^ k - 1) ≤ k * ppSum (g - 1) + (g ^ k - 1) / (g - 1) := by
  classical
  have hdvd : g - 1 ∣ g ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 k
  have hgk : 2 ≤ g ^ k := le_trans hg (Nat.le_self_pow hk g)
  have hN0 : g ^ k - 1 ≠ 0 := by omega
  have hg0 : g - 1 ≠ 0 := by omega
  have hNS : g ^ k - 1 = (g - 1) * ((g ^ k - 1) / (g - 1)) := (Nat.mul_div_cancel' hdvd).symm
  have hS0 : (g ^ k - 1) / (g - 1) ≠ 0 := by
    intro h; rw [h, mul_zero] at hNS; exact hN0 hNS
  unfold ppSum
  rw [← Finset.sum_filter_add_sum_filter_not (g ^ k - 1).primeFactors (fun p => p ∣ g - 1)]
  refine add_le_add ?_ ?_
  · calc ∑ p ∈ (g ^ k - 1).primeFactors with p ∣ g - 1, p ^ (g ^ k - 1).factorization p
        ≤ ∑ p ∈ (g ^ k - 1).primeFactors with p ∣ g - 1, k * p ^ (g - 1).factorization p := by
          apply Finset.sum_le_sum; intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          exact pp_lte hp.1.1 hg h4 hp.2 hk
      _ ≤ ∑ p ∈ (g - 1).primeFactors, k * p ^ (g - 1).factorization p := by
          apply Finset.sum_le_sum_of_subset
          intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          rw [Nat.mem_primeFactors]; exact ⟨hp.1.1, hp.2, hg0⟩
      _ = k * ∑ p ∈ (g - 1).primeFactors, p ^ (g - 1).factorization p := by rw [Finset.mul_sum]
  · calc ∑ p ∈ (g ^ k - 1).primeFactors with ¬ p ∣ g - 1, p ^ (g ^ k - 1).factorization p
        = ∑ p ∈ (g ^ k - 1).primeFactors with ¬ p ∣ g - 1,
            p ^ ((g ^ k - 1) / (g - 1)).factorization p := by
          apply Finset.sum_congr rfl; intro p hp
          rw [Finset.mem_filter] at hp
          conv_lhs => rw [hNS]
          rw [Nat.factorization_mul hg0 hS0, Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd hp.2, zero_add]
      _ ≤ ∑ p ∈ ((g ^ k - 1) / (g - 1)).primeFactors,
            p ^ ((g ^ k - 1) / (g - 1)).factorization p := by
          apply Finset.sum_le_sum_of_subset
          intro p hp
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          rw [Nat.mem_primeFactors]
          refine ⟨hp.1.1, ?_, hS0⟩
          have h1 : p ∣ (g - 1) * ((g ^ k - 1) / (g - 1)) := hNS ▸ hp.1.2.1
          exact (hp.1.1.dvd_mul.mp h1).resolve_left hp.2
      _ ≤ (g ^ k - 1) / (g - 1) := ppSum_le_self hS0

end PI.SqfRootShift.W
