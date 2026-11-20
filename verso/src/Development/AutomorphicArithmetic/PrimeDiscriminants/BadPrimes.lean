import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Introduce `p hp`. Rewrite `hp` using `[Nat.mem_primeFactors]`. Take `⟨hpp, hpd, -⟩` from `hp`. Establish `hc : p ∣ H.condN`. Break down `(Nat.Prime.dvd_mul hpp).1 hpd with h2 | h2` into its components or cases.

Rewrite using `[(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h2]`. Conclude with `H.two_dvd_condN`. Conclude with `H.der.discr_primes.1 p hpp (Int.natCast_dvd.2 h2)`. Break down `(H.dvd_condN_iff_small hpp).1 hc with h | h | h` into its components or cases. Conclude with `Finset.mem_union_left _ h`.

Simplify using `[h]`. Simplify using `[h]`.
-/
theorem bad_subset : Nat.primeFactors (2 * (discr H.E).natAbs) ⊆ H.small ∪ {H.q, H.d} := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hpd, -⟩ := hp
  have hc : p ∣ H.condN := by
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h2 | h2
    · rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h2]
      exact H.two_dvd_condN
    · exact H.der.discr_primes.1 p hpp (Int.natCast_dvd.2 h2)
  rcases (H.dvd_condN_iff_small hpp).1 hc with h | h | h
  · exact Finset.mem_union_left _ h
  · simp [h]
  · simp [h]

/- English proof (translation)
Rewrite using `[Finset.card_le_one]`. Introduce `p hp p' hp'`. Rewrite `hp`, `hp'` using `[Finset.mem_filter, H.mem_small_iff]`. Assume the negation of the conclusion as `hne`. Establish `hpn : R.n < p` using `by exact_mod_cast hB.trans_lt hp.2`.

Establish `hpn' : R.n < p'` using `by exact_mod_cast hB.trans_lt hp'.2`. Establish `hdvd : p * p' ∣ H.QS` using `Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp.1.1 hp'.1.1).2 hne) hp.1.2 hp'.1.2`. Establish `hle` using `Nat.le_of_dvd H.QS_pos hdvd`. Establish `hq` using `H.QS_le`. Establish `hm : R.n * R.n < p * p'` using `Nat.mul_lt_mul'' hpn hpn'`.

Rewrite `hq` using `[sq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem card_small_gt_le_one {B : ℝ} (hB : (R.n : ℝ) ≤ B) : (H.small.filter fun p : ℕ => B < (p : ℝ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp p' hp'
  rw [Finset.mem_filter, H.mem_small_iff] at hp hp'
  by_contra hne
  have hpn : R.n < p := by exact_mod_cast hB.trans_lt hp.2
  have hpn' : R.n < p' := by exact_mod_cast hB.trans_lt hp'.2
  have hdvd : p * p' ∣ H.QS :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp.1.1 hp'.1.1).2 hne) hp.1.2 hp'.1.2
  have hle := Nat.le_of_dvd H.QS_pos hdvd
  have hq := H.QS_le
  have hm : R.n * R.n < p * p' := Nat.mul_lt_mul'' hpn hpn'
  rw [sq] at hq
  linarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Distinguish the cases in `hs : p ∈ H.small`.

Conclude with `Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hs, hp.2⟩)`. Conclude with `Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hp.1, hs⟩)`. Use `_ ≤ (S \ H.small).card + (H.small.filter fun p : ℕ => B < (p : ℝ)).card := Finset.card_union_le _ _`. Use `_ ≤ (S \ H.small).card + 1 := by`. Establish `h1` using `card_small_gt_le_one H hB`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_gt_le_card_sdiff (S : Finset ℕ) {B : ℝ} (hB : (R.n : ℝ) ≤ B) :
    (S.filter fun p : ℕ => B < (p : ℝ)).card ≤ (S \ H.small).card + 1 := by
  calc (S.filter fun p : ℕ => B < (p : ℝ)).card
      ≤ ((S \ H.small) ∪ H.small.filter fun p : ℕ => B < (p : ℝ)).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_filter] at hp
        by_cases hs : p ∈ H.small
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hs, hp.2⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hp.1, hs⟩)
    _ ≤ (S \ H.small).card + (H.small.filter fun p : ℕ => B < (p : ℝ)).card :=
        Finset.card_union_le _ _
    _ ≤ (S \ H.small).card + 1 := by
        have h1 := card_small_gt_le_one H hB
        omega

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_sdiff, Finset.mem_union]`. Break down `hp.1 with h | h` into its components or cases.

Establish `hb` using `bad_subset H h`. Rewrite `hb` using `[Finset.mem_union]`. Break down `hb with h' | h'` into its components or cases. Conclude with `absurd h' hp.2`. Conclude with `Finset.mem_union_right _ h'`.

Conclude with `Finset.mem_union_left _ h`. Use `_ ≤ S.card + ({H.q, H.d} : Finset ℕ).card := Finset.card_union_le _ _`. Use `_ ≤ S.card + 2 := by`. Establish `h2 : ({H.q, H.d} : Finset ℕ).card ≤ 2` using `Finset.card_le_two`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_bad_sdiff_le (S : Finset ℕ) :
    ((Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) \ H.small).card ≤ S.card + 2 := by
  calc _ ≤ (S ∪ {H.q, H.d}).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Finset.mem_sdiff, Finset.mem_union] at hp
        rcases hp.1 with h | h
        · have hb := bad_subset H h
          rw [Finset.mem_union] at hb
          rcases hb with h' | h'
          · exact absurd h' hp.2
          · exact Finset.mem_union_right _ h'
        · exact Finset.mem_union_left _ h
    _ ≤ S.card + ({H.q, H.d} : Finset ℕ).card := Finset.card_union_le _ _
    _ ≤ S.card + 2 := by
        have h2 : ({H.q, H.d} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        omega

/- English proof (translation)
Use `H.card_gt_le_card_sdiff (Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) hB` as an intermediate fact. Use `H.card_bad_sdiff_le S` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem card_bad_gt_le (S : Finset ℕ) {B : ℝ} (hB : (R.n : ℝ) ≤ B) :
    ((Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S).filter fun p : ℕ => B < (p : ℝ)).card ≤ S.card + 3 := by
  have := H.card_gt_le_card_sdiff (Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S) hB
  have := H.card_bad_sdiff_le S
  omega

/- English proof (translation)
Establish `h1 : (4 : ℝ) * (R.n : ℝ) ≤ H.rdE ^ 2` using `H.der.rd_sq_ge`. Establish `hn : (0 : ℝ) < R.n` using `by exact_mod_cast R.toFrame.ord_pos`. Establish `h2 : (R.n : ℝ) ≤ H.rdE ^ 2` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_n_le_two_log_rdE : Real.log (R.n : ℝ) ≤ 2 * Real.log H.rdE := by
  have h1 : (4 : ℝ) * (R.n : ℝ) ≤ H.rdE ^ 2 := H.der.rd_sq_ge
  have hn : (0 : ℝ) < R.n := by exact_mod_cast R.toFrame.ord_pos
  have h2 : (R.n : ℝ) ≤ H.rdE ^ 2 := by linarith
  calc Real.log R.n ≤ Real.log (H.rdE ^ 2) := Real.log_le_log hn h2
    _ = 2 * Real.log H.rdE := by
      rw [Real.log_pow]
      push_cast
      ring

/- English proof (translation)
Establish `hprod : ∏ p ∈ H.small, p ≤ H.QS` using `Nat.le_of_dvd H.QS_pos (Nat.prod_primeFactors_dvd _)`. Establish `hpos : ∀ p ∈ H.small, (0 : ℝ) < p` using `fun p hp => by`. Establish `hp'` using `((H.mem_small_iff).1 hp).1.pos`. Conclude with `hp'` after adjusting the coercions. Rewrite using `[← Real.log_prod (s := H.small) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (hpos p hp).ne')]`.

Establish `hP : (0 : ℝ) < ∏ p ∈ H.small, (p : ℝ)` using `Finset.prod_pos hpos`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.log_le_log hP` to reduce the goal to its premises. Establish `h' : (∏ p ∈ H.small, p : ℕ) ≤ R.n ^ 2` using `hprod.trans H.QS_le`. Establish `h''` using `(Nat.cast_le (α := ℝ)).2 h'`.

Move the coercions through the operations in `at h''`. Conclude with `h''`. Use `_ = 2 * Real.log R.n := by`. Rewrite using `[Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 4 * Real.log H.rdE := by`. Establish `h6` using `log_n_le_two_log_rdE H`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_small_log_le : ∑ p ∈ H.small, Real.log p ≤ 4 * Real.log H.rdE := by
  have hprod : ∏ p ∈ H.small, p ≤ H.QS := Nat.le_of_dvd H.QS_pos (Nat.prod_primeFactors_dvd _)
  have hpos : ∀ p ∈ H.small, (0 : ℝ) < p := fun p hp => by
    have hp' := ((H.mem_small_iff).1 hp).1.pos
    exact_mod_cast hp'
  rw [← Real.log_prod (s := H.small) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (hpos p hp).ne')]
  have hP : (0 : ℝ) < ∏ p ∈ H.small, (p : ℝ) := Finset.prod_pos hpos
  calc Real.log (∏ p ∈ H.small, (p : ℝ)) ≤ Real.log ((R.n : ℝ) ^ 2) := by
        apply Real.log_le_log hP
        have h' : (∏ p ∈ H.small, p : ℕ) ≤ R.n ^ 2 := hprod.trans H.QS_le
        have h'' := (Nat.cast_le (α := ℝ)).2 h'
        push_cast at h''
        exact h''
    _ = 2 * Real.log R.n := by
        rw [Real.log_pow]
        push_cast
        ring
    _ ≤ 4 * Real.log H.rdE := by
        have h6 := log_n_le_two_log_rdE H
        linarith

end Formalism.BasicNotions.Host
