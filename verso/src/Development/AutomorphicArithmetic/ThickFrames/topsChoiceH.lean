import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AutomorphicArithmetic.ThickFrames.topsBase

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

/- English proof (translation)
Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `hk` using `hs p hp hle`. Establish `hc'` using `hc`. Simplify using `only [Host.cls, primeClass] at hc'`.

Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Establish `hmem : 2 ∈ H.toHostRaw.small`. Rewrite using `[Formalism.HC.HostRaw.small, Nat.mem_primeFactors]`. Use `⟨Nat.prime_two, ?_, H.QS_pos.ne'⟩` and prove the remaining obligations.

Conclude with `dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd`. Rewrite `hc'` using `[if_pos hmem]`. Conclude with `absurd hc' (by decide)`. Establish `hodd : p.factorization 2 = 0` using `Nat.factorization_eq_zero_of_not_dvd (fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)`. Simplify using `only [GlobalTheoryTheory.kronSym, hodd, pow_zero, Nat.div_one, mul_one] at hk`.

Apply the tactic sequence `split_ifs at hc' <;> simp_all`.
-/
private theorem lt_of_classC0' {R : Ranks} (H : Host R) {p : ℕ} {y : ℝ} (hp : p.Prime) (hc : H.cls p = PrimeClass.inertClass)
    (hs : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1) : y < p := by
  by_contra hle
  push_neg at hle
  have hk := hs p hp hle
  have hc' := hc
  simp only [Host.cls, primeClass] at hc'
  by_cases h2 : p = 2
  · subst h2
    have hmem : 2 ∈ H.toHostRaw.small := by
      rw [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, ?_, H.QS_pos.ne'⟩
      exact dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd
    rw [if_pos hmem] at hc'
    exact absurd hc' (by decide)
  · have hodd : p.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
    simp only [GlobalTheoryTheory.kronSym, hodd, pow_zero, Nat.div_one, mul_one] at hk
    split_ifs at hc' <;> simp_all

/- English proof (translation)
Introduce `eps C8 heps heps52`. Take `⟨Cb, x0, hCb, hT⟩` from `topsBase eps (max C8 2) heps heps52 (le_trans (by norm_num) (le_max_right _ _))`. Use `⟨Cb, x0, hCb, ?_⟩` and prove the remaining obligations. Introduce `s R H hse hx hRV hHC hex`. Take `⟨Y, hPW, hPR⟩` from `hex`.

Take `⟨⟨hn1, hn2⟩, _, ⟨hk1, hk2⟩, _⟩` from `hRV`. Take `⟨hJ, ho, hQS⟩` from `hHC`. Rewrite `hn1`, `hn2`, `hk1`, `hk2`, `hPR` using `[hse]`. Establish `hCo1 : C8 ≤ max C8 2` using `le_max_left _ _`. Establish `hCo2 : (2 : ℝ) ≤ max C8 2` using `le_max_right _ _`.

Establish `hx1 : 1 < s.x` using `s.one_lt_alt`. Establish `hJ1 : 1 ≤ s.J` using `s.one_le_J`. Establish `hkron` using `hPR.2.2.2.2.2.2.2.2.2.1`. Establish `hsmall : s.x ^ (eps / (5 * max C8 2)) ≤ Y ^ (eps / 5)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Real.rpow_mul (by linarith)]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (s.x ^ (1 / s.J)) ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) (Real.rpow_le_rpow_of_exponent_le hx1.le (one_div_le_one_div_of_le (by linarith) (by linarith))) (by positivity)`. Use `_ ≤ Y ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hPW.1 (by positivity)`.

Establish `hC0 : ∀ p : ℕ, p.Prime → (baseOf s 0 0 H).IsResidueClassZero p → s.x ^ (eps / (5 * max C8 2)) < p`. Introduce `p hp hc`. Conclude with `lt_of_le_of_lt hsmall (lt_of_classC0' H hp hc hkron)`. Establish `hxe : 0 ≤ s.x ^ (2 + 8 * eps)` using `Real.rpow_nonneg (by linarith) _`. Take `⟨TT, h1, h2, h3, h4⟩` from `hT (baseOf s 0 0 H) (hPH H) hse hx (by show s.x ^ (2 + 8 * eps) / 2 ≤ (R.n : ℝ) linarith) (le_trans hn2 (mul_le_mul_of_nonneg_right hCo2 hxe)) (le_trans ho hCo1) hk2 hC0`.

Conclude with `⟨TT, h1, h2, h4, h3⟩`.
-/
theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsChoiceH :
    ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x0 : ℝ, 0 < Cb ∧ ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x →
      RankVal s R → HostConst s C8 H → (∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H) →
      ∃ TT : Finset R.A, s.delta1 * R.n / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * R.n ∧
        BadOK s Cb { H with TT := TT } ∧ R.toFrame.Shares TT (s.x ^ (-1 + eps)) := by
  intro eps C8 heps heps52
  obtain ⟨Cb, x0, hCb, hT⟩ := topsBase eps (max C8 2) heps heps52
    (le_trans (by norm_num) (le_max_right _ _))
  refine ⟨Cb, x0, hCb, ?_⟩
  intro s R H hse hx hRV hHC hex
  obtain ⟨Y, hPW, hPR⟩ := hex
  obtain ⟨⟨hn1, hn2⟩, _, ⟨hk1, hk2⟩, _⟩ := hRV
  obtain ⟨hJ, ho, hQS⟩ := hHC
  rw [hse] at hn1 hn2 hk1 hk2 hPR
  have hCo1 : C8 ≤ max C8 2 := le_max_left _ _
  have hCo2 : (2 : ℝ) ≤ max C8 2 := le_max_right _ _
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ1 : 1 ≤ s.J := s.one_le_J
  have hkron := hPR.2.2.2.2.2.2.2.2.2.1
  have hsmall : s.x ^ (eps / (5 * max C8 2)) ≤ Y ^ (eps / 5) := by
    calc s.x ^ (eps / (5 * max C8 2)) = (s.x ^ (1 / max C8 2)) ^ (eps / 5) := by
          rw [← Real.rpow_mul (by linarith)]
          congr 1
          field_simp
      _ ≤ (s.x ^ (1 / s.J)) ^ (eps / 5) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_le_rpow_of_exponent_le hx1.le
              (one_div_le_one_div_of_le (by linarith) (by linarith))) (by positivity)
      _ ≤ Y ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hPW.1 (by positivity)
  have hC0 : ∀ p : ℕ, p.Prime → (baseOf s 0 0 H).IsResidueClassZero p → s.x ^ (eps / (5 * max C8 2)) < p := by
    intro p hp hc
    exact lt_of_le_of_lt hsmall (lt_of_classC0' H hp hc hkron)
  have hxe : 0 ≤ s.x ^ (2 + 8 * eps) := Real.rpow_nonneg (by linarith) _
  obtain ⟨TT, h1, h2, h3, h4⟩ := hT (baseOf s 0 0 H) (hPH H) hse hx (by
      show s.x ^ (2 + 8 * eps) / 2 ≤ (R.n : ℝ)
      linarith)
    (le_trans hn2 (mul_le_mul_of_nonneg_right hCo2 hxe)) (le_trans ho hCo1) hk2 hC0
  exact ⟨TT, h1, h2, h4, h3⟩
