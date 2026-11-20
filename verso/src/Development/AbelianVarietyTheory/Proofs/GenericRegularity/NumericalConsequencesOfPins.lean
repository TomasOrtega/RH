import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.DimAddCardFlagVar
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.PinNum

/- English proof (translation)
Establish `hodd` using `l.odd`. Rewrite `hodd` using `[hM, Nat.odd_mul]`. Establish `ha3 : 3 ≤ a`. Use `ha.two_le` as an intermediate fact. Take `⟨k, hk⟩` from `hodd.1`.

Use linear arithmetic over natural numbers and integers. Establish `hb3 : 3 ≤ b`. Use `hb.two_le` as an intermediate fact. Take `⟨k, hk⟩` from `hodd.2`. Use linear arithmetic over natural numbers and integers.

Unfold `Level.GoodAt`. Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`. Distinguish the cases in `hp : p.Prime`. Use `swap`. Simplify `l.three_le` using `[Nat.factorization_eq_zero_of_not_prime _ hp]`.

Establish `key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p` using `fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))`. Distinguish the cases in `h : p ∣ a`. Use `key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_` and prove the remaining obligations. Conclude with `Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'`. Conclude with `key a ha3 (hM ▸ dvd_mul_right _ _) h`.
-/
theorem goodAt_of_two_primes {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hM : l.M = a * b) (p : ℕ) : l.GoodAt p := by
  have hodd := l.odd
  rw [hM, Nat.odd_mul] at hodd
  have ha3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨k, hk⟩ := hodd.1
    omega
  have hb3 : 3 ≤ b := by
    have := hb.two_le
    obtain ⟨k, hk⟩ := hodd.2
    omega
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  by_cases hp : p.Prime
  swap
  · simpa [Nat.factorization_eq_zero_of_not_prime _ hp] using l.three_le
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'
  · exact key a ha3 (hM ▸ dvd_mul_right _ _) h

/- English proof (translation)
Establish `h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ)`. Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h` after adjusting the coercions.
-/
theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  exact_mod_cast h

/- English proof (translation)
Take `⟨-, -, h3, -⟩` from `h`. Establish `hsq` using `Q.H.sqrt_neg_disc_sq`. Rewrite `hsq` using `[h3]`. Establish `hd : (1 : ℝ) ≤ Q.H.d` using `by exact_mod_cast Q.H.d_prime.one_le`. Establish `hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d`.

Rewrite using `[← norm_pow, hsq, norm_neg, Complex.norm_natCast]`. Establish `h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use polynomial arithmetic with `[norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]`.

Establish `hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ)`. Establish `: Ideal.absNorm D.host.ccK ≠ 0` using `fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `Nat.one_le_iff_ne_zero.2 this` after adjusting the coercions. Establish `hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖)`. Unfold `xiR Formalism.BasicNotions.Host.xi0`.

Rewrite using `[map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast]`. Establish `h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖` using `one_le_mul_of_one_le_of_one_le hN h1`. Rewrite using `[hx]`. Conclude with `⟨by positivity, (div_le_one (by positivity)).2 h2⟩`.
-/
theorem xiR_pos_le_one (D : D7) (Q : Par D) (h : Q.PinHost) : 0 < xiR D ∧ xiR D ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := h
  have hsq := Q.H.sqrt_neg_disc_sq
  rw [h3] at hsq
  have hd : (1 : ℝ) ≤ Q.H.d := by exact_mod_cast Q.H.d_prime.one_le
  have hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d := by
    rw [← norm_pow, hsq, norm_neg, Complex.norm_natCast]
  have h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖) := by
    unfold xiR Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_natCast]
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    one_le_mul_of_one_le_of_one_le hN h1
  rw [hx]
  exact ⟨by positivity, (div_le_one (by positivity)).2 h2⟩

/- English proof (translation)
Introduce `D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩`. Establish `hx` using `xiR_pos_le_one D Q hH`. Use `⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_, hx.1, hx.2, finrank_host D, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[Level.M', hA, Nat.lcm_one_right]`. Take `⟨hp, hq, -⟩` from `hD j hj`.

Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨hj1, hj2⟩` from `hj`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp, hq]`. Simplify using `only [Ranks.sigW, Ranks.r]`.

Use linear arithmetic over natural numbers and integers. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Rewrite using `[GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]`. Both sides reduce to the same expression.
-/
theorem numerics_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  intro D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩
  have hx := xiR_pos_le_one D Q hH
  refine ⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_,
    hx.1, hx.2, finrank_host D, fun j hj => ?_⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
  · obtain ⟨hp, hq, -⟩ := hD j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      omega
    · unfold Ranks.r
      omega
    · rw [GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]
      rfl

end GlobalTheory.PinNum
