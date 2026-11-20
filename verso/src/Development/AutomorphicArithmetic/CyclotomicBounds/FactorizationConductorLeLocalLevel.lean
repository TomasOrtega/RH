import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

namespace UpperTheory.KStar.S0

open Formalism.BasicNotions

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

/- English proof (translation)
Establish `h1` using `H.tower_dvd`. Establish `h2 : 2 ^ (R.e + 2) ∣ H.QS` using `h1`. Rewrite `h2` using `[Nat.prime_two.pow_dvd_iff_le_factorization H.QS_pos.ne']`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_factorization (H : Host R) : 2 ≤ H.QS.factorization 2 := by
  have h1 := H.tower_dvd
  have h2 : 2 ^ (R.e + 2) ∣ H.QS := h1
  rw [Nat.prime_two.pow_dvd_iff_le_factorization H.QS_pos.ne'] at h2
  omega

/- English proof (translation)
Distinguish the cases in `h2 : N.l i = 2`. Use `two_le_factorization H` as an intermediate fact. Rewrite using `[N.restNLevelExponent_of_two i h2, h2, max_eq_right (by omega)]`. Conclude with `N.restNLevelExponent_of_odd i h2`.
-/
theorem localLevel_eq_max_one_factorization : N.s0 i = max 1 (H.QS.factorization (N.l i)) := by
  by_cases h2 : N.l i = 2
  · have := two_le_factorization H
    rw [N.restNLevelExponent_of_two i h2, h2, max_eq_right (by omega)]
  · exact N.restNLevelExponent_of_odd i h2

/- English proof (translation)
Rewrite using `[localLevel_eq_max_one_factorization]`. Conclude with `le_max_left _ _`.
-/
theorem one_le_localLevel : 1 ≤ N.s0 i := by rw [localLevel_eq_max_one_factorization]; exact le_max_left _ _

/- English proof (translation)
Rewrite using `[N.restNLevelExponent_of_two i h]`. Conclude with `two_le_factorization H`.
-/
theorem two_le_localLevel_of_eq_two (h : N.l i = 2) : 2 ≤ N.s0 i := by rw [N.restNLevelExponent_of_two i h]; exact two_le_factorization H

/- English proof (translation)
Use `haveI := N.lPrime i`. Establish `hl : (N.l i).Prime` using `Fact.out`. Take `⟨hq, hd, hq8, hd16, -⟩` from `H.hyp`. Establish `hqd : H.q ≠ H.d`. Introduce `h`.

Rewrite `hq8` using `[h]`. Use linear arithmetic over natural numbers and integers. Establish `hQS : H.QS ≠ 0` using `H.QS_pos.ne'`. Establish `hcop` using `H.QS_coprime`. Establish `notdvd : N.l i ∣ H.q * H.d → ¬ N.l i ∣ H.QS`.

Introduce `h1 h2`. Establish `h3 : N.l i ∣ Nat.gcd H.QS (H.q * H.d)` using `Nat.dvd_gcd h2 h1`. Rewrite `h3` using `[hcop]`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp h3)`. Establish `e1 : H.condN.factorization (N.l i) = H.QS.factorization (N.l i) + (H.q.factorization (N.l i) + H.d.factorization (N.l i))` using `by show (H.QS * H.q * H.d).factorization (N.l i) = _`.

Rewrite using `[mul_assoc, Nat.factorization_mul hQS (mul_ne_zero hq.ne_zero hd.ne_zero), Nat.factorization_mul hq.ne_zero hd.ne_zero]`. Simplify using the standard rewrite rules. Rewrite using `[e1, localLevel_eq_max_one_factorization N i, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]`. Distinguish the cases in `hlq : H.q = N.l i`. Establish `hz` using `Nat.factorization_eq_zero_of_not_dvd (notdvd (hlq ▸ dvd_mul_right _ _))`.

Establish `hdl : H.d ≠ N.l i` using `fun h => hqd (hlq.trans h.symm)`. Rewrite using `[hz, if_pos hlq, if_neg hdl]`. Conclude with `le_max_left _ _`. Distinguish the cases in `hld : H.d = N.l i`. Establish `hz` using `Nat.factorization_eq_zero_of_not_dvd (notdvd (hld ▸ dvd_mul_left _ _))`.

Rewrite using `[hz, if_neg hlq, if_pos hld]`. Conclude with `le_max_left _ _`. Rewrite using `[if_neg hlq, if_neg hld]`. Simplify using the standard rewrite rules.
-/
theorem factorization_conductor_le_localLevel : H.condN.factorization (N.l i) ≤ N.s0 i := by
  haveI := N.lPrime i
  have hl : (N.l i).Prime := Fact.out
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hqd : H.q ≠ H.d := by
    intro h
    rw [h] at hq8
    omega
  have hQS : H.QS ≠ 0 := H.QS_pos.ne'
  have hcop := H.QS_coprime
  have notdvd : N.l i ∣ H.q * H.d → ¬ N.l i ∣ H.QS := by
    intro h1 h2
    have h3 : N.l i ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd h2 h1
    rw [hcop] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  have e1 : H.condN.factorization (N.l i) =
      H.QS.factorization (N.l i) + (H.q.factorization (N.l i) + H.d.factorization (N.l i)) := by
    show (H.QS * H.q * H.d).factorization (N.l i) = _
    rw [mul_assoc, Nat.factorization_mul hQS (mul_ne_zero hq.ne_zero hd.ne_zero),
      Nat.factorization_mul hq.ne_zero hd.ne_zero]
    simp
  rw [e1, localLevel_eq_max_one_factorization N i, hq.factorization, hd.factorization, Finsupp.single_apply, Finsupp.single_apply]
  by_cases hlq : H.q = N.l i
  · have hz := Nat.factorization_eq_zero_of_not_dvd (notdvd (hlq ▸ dvd_mul_right _ _))
    have hdl : H.d ≠ N.l i := fun h => hqd (hlq.trans h.symm)
    rw [hz, if_pos hlq, if_neg hdl]
    exact le_max_left _ _
  · by_cases hld : H.d = N.l i
    · have hz := Nat.factorization_eq_zero_of_not_dvd (notdvd (hld ▸ dvd_mul_left _ _))
      rw [hz, if_neg hlq, if_pos hld]
      exact le_max_left _ _
    · rw [if_neg hlq, if_neg hld]
      simp

end UpperTheory.KStar.S0
