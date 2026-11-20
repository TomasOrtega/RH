import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Set `v : AbsoluteValue K ℝ` to `NormedField.toAbsoluteValue K`. Establish `hv : ∀ a, v a = ‖a‖` using `fun _ => rfl`. Establish `hna : IsNonarchimedean v` using `fun a b => IsUltrametricDist.norm_add_le_max a b`. Use `⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_, fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q, fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify `le_gaussNorm v p zero_le_one i` using `[hv]`.

Take `⟨i, hi⟩` from `exists_eq_gaussNorm v 1 p`. Rewrite using `[hi, hv, one_pow, mul_one]`. Conclude with `hr i`. Rewrite using `[gaussNorm_C, hv]`. Rewrite using `[← monomial_one_one_eq_X, gaussNorm_monomial, hv]`.

Simplify using the standard rewrite rules.
-/
theorem exists_gauss_size_polynomial (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by
  let v : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have hv : ∀ a, v a = ‖a‖ := fun _ => rfl
  have hna : IsNonarchimedean v := fun a b => IsUltrametricDist.norm_add_le_max a b
  refine ⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_,
    fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q,
    fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩
  · simpa [hv] using le_gaussNorm v p zero_le_one i
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v 1 p
    rw [hi, hv, one_pow, mul_one]
    exact hr i
  · rw [gaussNorm_C, hv]
  · rw [← monomial_one_one_eq_X, gaussNorm_monomial, hv]
    simp

/- English proof (translation)
Introduce `K _ _ A B A' B' n h hA hB hA' hB' hh heq`. Take `⟨G, h0, hle, hub, hmul, hadd, hC, hX⟩` from `exists_gauss_size_polynomial K`. Establish `hone : G 1 = 1` using `by simpa using hC 1`. Establish `hpow : ∀ p (k : ℕ), G (p ^ k) = G p ^ k`. Introduce `p k`.

Proceed by induction on `k with`. Consider the case `zero => simpa using hone`. Consider the case `succ k ih => rw [pow_succ, hmul, ih, pow_succ]`. Establish `hneg : ∀ p, G (-p) ≤ G p` using `fun p => hub _ _ fun i => by rw [coeff_neg, norm_neg]; exact hle p i`. Establish `hadd' : ∀ p q r, G p ≤ r → G q ≤ r → G (p + q) ≤ r` using `fun p q r hp hq => (hadd p q).trans (max_le hp hq)`.

Establish `hsub : ∀ p q r, G p ≤ r → G q ≤ r → G (p - q) ≤ r` using `fun p q r hp hq => by`. Rewrite using `[sub_eq_add_neg]`. Conclude with `hadd' _ _ _ hp ((hneg q).trans hq)`. Establish `hmul' : ∀ p q r s, G p ≤ r → G q ≤ s → G (p * q) ≤ r * s` using `fun p q r s hp hq => by`. Rewrite using `[hmul]`.

Conclude with `mul_le_mul hp hq (h0 q) ((h0 p).trans hp)`. Establish `hpow' : ∀ p r (k : ℕ), G p ≤ r → G (p ^ k) ≤ r ^ k` using `fun p r k hp => by`. Rewrite using `[hpow]`. Conclude with `pow_le_pow_left₀ (h0 p) hp k`. Establish `hder : ∀ p, G (derivative p) ≤ G p` using `fun p => hub _ _ fun i => by`.

Rewrite using `[coeff_derivative, norm_mul]`. Establish `h1 : ‖((i : K) + 1)‖ ≤ 1`. Conclude with `IsUltrametricDist.norm_natCast_le_one K (i + 1)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `hh1 : G h ≤ 1` using `hub _ _ hh`.

It suffices to establish `hn : G n ≤ 1 from fun i => (hle n i).trans hn`. Assume the negation of the conclusion as `hg`. Use `push Not at hg`. Use `set g := G n with hgdef`. Establish `hX1 : G X ≤ 1` using `hX.le`.

Establish `hcub : G (X ^ 3 + C A * X + C B) ≤ 1`. Use `hadd' _ _ _ (hadd' _ _ _ ?_ ?_) ?_` and prove the remaining obligations. Simplify using `using hpow' X 1 3 hX1`. Simplify using `using hmul' (C A) X 1 1 (by rw [hC]; exact hA) hX1`. Rewrite using `[hC]`.

Conclude with `hB`. Establish `h2n : G (2 * n) ≤ g`. Rewrite using `[two_mul]`. Conclude with `hadd' _ _ _ le_rfl le_rfl`. Establish `hW : G (derivative n * h - 2 * n * derivative h) ≤ g`.

Use `hsub _ _ _ ?_ ?_` and prove the remaining obligations. Simplify using `using hmul' _ _ g 1 (hder n) hh1`. Simplify using `using hmul' _ _ g 1 h2n ((hder h).trans hh1)`. Establish `hL : G ((X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2) ≤ g ^ 2`. Simplify using `using hmul' _ _ 1 (g ^ 2) hcub (hpow' _ g 2 hW)`.

Establish `hgg : g ≤ g ^ 2` using `by nlinarith`. Establish `h1g : 1 ≤ g ^ 2` using `hg.le.trans hgg`. Establish `hA2 : G (C A' * n * h ^ 4) ≤ g ^ 2`. Use `le_trans ?_ hgg` and prove the remaining obligations. Simplify using `using hmul' _ _ (1 * g) (1 ^ 4) (hmul' (C A') n 1 g (by rw [hC]; exact hA') le_rfl) (hpow' h 1 4 hh1)`.

Establish `hB2 : G (C B' * h ^ 6) ≤ g ^ 2`. Use `le_trans ?_ h1g` and prove the remaining obligations. Simplify using `using hmul' (C B') _ 1 (1 ^ 6) (by rw [hC]; exact hB') (hpow' h 1 6 hh1)`. Establish `hn3 : n ^ 3 = (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 - C A' * n * h ^ 4 - C B' * h ^ 6`. Rewrite using `[heq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : G (n ^ 3) ≤ g ^ 2`. Rewrite using `[hn3]`. Conclude with `hsub _ _ _ (hsub _ _ _ hL hA2) hB2`. Rewrite `h3` using `[hpow, ← hgdef]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem isogeny_numerator_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (A B A' B' : K) (n h : K[X]),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → (∀ i, ‖h.coeff i‖ ≤ 1) →
      (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
        = n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6 → ∀ i, ‖n.coeff i‖ ≤ 1 := by
  intro K _ _ A B A' B' n h hA hB hA' hB' hh heq
  obtain ⟨G, h0, hle, hub, hmul, hadd, hC, hX⟩ := exists_gauss_size_polynomial K
  have hone : G 1 = 1 := by simpa using hC 1
  have hpow : ∀ p (k : ℕ), G (p ^ k) = G p ^ k := by
    intro p k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hneg : ∀ p, G (-p) ≤ G p := fun p =>
    hub _ _ fun i => by rw [coeff_neg, norm_neg]; exact hle p i
  have hadd' : ∀ p q r, G p ≤ r → G q ≤ r → G (p + q) ≤ r := fun p q r hp hq =>
    (hadd p q).trans (max_le hp hq)
  have hsub : ∀ p q r, G p ≤ r → G q ≤ r → G (p - q) ≤ r := fun p q r hp hq => by
    rw [sub_eq_add_neg]
    exact hadd' _ _ _ hp ((hneg q).trans hq)
  have hmul' : ∀ p q r s, G p ≤ r → G q ≤ s → G (p * q) ≤ r * s := fun p q r s hp hq => by
    rw [hmul]
    exact mul_le_mul hp hq (h0 q) ((h0 p).trans hp)
  have hpow' : ∀ p r (k : ℕ), G p ≤ r → G (p ^ k) ≤ r ^ k := fun p r k hp => by
    rw [hpow]
    exact pow_le_pow_left₀ (h0 p) hp k
  have hder : ∀ p, G (derivative p) ≤ G p := fun p =>
    hub _ _ fun i => by
      rw [coeff_derivative, norm_mul]
      have h1 : ‖((i : K) + 1)‖ ≤ 1 := by
        exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (i + 1)
      calc ‖p.coeff (i + 1)‖ * ‖((i : K) + 1)‖ ≤ G p * 1 :=
            mul_le_mul (hle p _) h1 (norm_nonneg _) (h0 p)
        _ = G p := mul_one _
  have hh1 : G h ≤ 1 := hub _ _ hh
  suffices hn : G n ≤ 1 from fun i => (hle n i).trans hn
  by_contra hg
  push Not at hg
  set g := G n with hgdef
  have hX1 : G X ≤ 1 := hX.le
  have hcub : G (X ^ 3 + C A * X + C B) ≤ 1 := by
    refine hadd' _ _ _ (hadd' _ _ _ ?_ ?_) ?_
    · simpa using hpow' X 1 3 hX1
    · simpa using hmul' (C A) X 1 1 (by rw [hC]; exact hA) hX1
    · rw [hC]; exact hB
  have h2n : G (2 * n) ≤ g := by
    rw [two_mul]
    exact hadd' _ _ _ le_rfl le_rfl
  have hW : G (derivative n * h - 2 * n * derivative h) ≤ g := by
    refine hsub _ _ _ ?_ ?_
    · simpa using hmul' _ _ g 1 (hder n) hh1
    · simpa using hmul' _ _ g 1 h2n ((hder h).trans hh1)
  have hL : G ((X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2)
      ≤ g ^ 2 := by
    simpa using hmul' _ _ 1 (g ^ 2) hcub (hpow' _ g 2 hW)
  have hgg : g ≤ g ^ 2 := by nlinarith
  have h1g : 1 ≤ g ^ 2 := hg.le.trans hgg
  have hA2 : G (C A' * n * h ^ 4) ≤ g ^ 2 := by
    refine le_trans ?_ hgg
    simpa using hmul' _ _ (1 * g) (1 ^ 4)
      (hmul' (C A') n 1 g (by rw [hC]; exact hA') le_rfl) (hpow' h 1 4 hh1)
  have hB2 : G (C B' * h ^ 6) ≤ g ^ 2 := by
    refine le_trans ?_ h1g
    simpa using hmul' (C B') _ 1 (1 ^ 6) (by rw [hC]; exact hB') (hpow' h 1 6 hh1)
  have hn3 : n ^ 3 = (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
      - C A' * n * h ^ 4 - C B' * h ^ 6 := by
    rw [heq]; ring
  have h3 : G (n ^ 3) ≤ g ^ 2 := by
    rw [hn3]
    exact hsub _ _ _ (hsub _ _ _ hL hA2) hB2
  rw [hpow, ← hgdef] at h3
  nlinarith

end GlobalTheory
