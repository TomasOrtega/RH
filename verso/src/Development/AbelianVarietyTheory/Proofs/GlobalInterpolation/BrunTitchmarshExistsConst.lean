import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrimeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

/- English proof (translation)
Use `haveI := Fact.mk hl`. Establish `hq' : (q : ZMod l) ≠ 0` using `fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)`. Use `⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_dvd_mul_add_of_prime (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

/- English proof (translation)
Establish `hdec : ∀ p ∈ P, p = q * (p / q) + a % q` using `fun p hp => by`. Establish `h : p % q = a % q` using `(hP p hp).2.1`. Rewrite using `[← h, Nat.div_add_mod]`. Establish `hinj : Set.InjOn (fun p => p / q + 1) (P : Set ℕ)`. Introduce `p hp p' hp' h`.

Establish `h' : p / q = p' / q` using `by simpa using h`. Rewrite using `[hdec p hp, hdec p' hp', h']`. Establish `key` using `GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime M N Q q (P.image fun p => p / q + 1) hQ hq ?_ ?_`. Rewrite `key` using `[Finset.card_image_of_injOn hinj]`. Then use the resulting hypothesis. Introduce `n hn`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hn`. Take `⟨-, -, -, h1, h2⟩` from `hP p hp`. Establish `h3 : M ≤ p / q` using `(Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm])`. Establish `h4 : p / q < M + N` using `(Nat.div_lt_iff_lt_mul hq).2 (by rwa [mul_comm])`. Conclude with `Finset.mem_Ioc.2 ⟨by omega, by omega⟩`.

Introduce `l hl hlQ hlq`. Take `⟨c, hc⟩` from `exists_dvd_mul_add_of_prime l q (a % q) hl hlq`. Use `⟨c + 1, fun n hn h => ?_⟩` and prove the remaining obligations. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hn`. Establish `h1 : p / q ≡ c [MOD l]` using `Nat.ModEq.add_right_cancel' 1 h`.

Establish `h2 : q * (p / q) + a % q ≡ q * c + a % q [MOD l]` using `(h1.mul_left q).add_right _`. Rewrite `h2` using `[← hdec p hp]`. Establish `h3 : l ∣ p` using `(Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 hc))`. Establish `h4` using `(Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).1 h3`. Use `(hP p hp).2.2.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_large_primes_class_le (q a Q M N : ℕ) (P : Finset ℕ) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≡ a [MOD q] ∧ Q < p ∧ q * M ≤ p ∧ p < q * (M + N)) :
    (P.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  have hdec : ∀ p ∈ P, p = q * (p / q) + a % q := fun p hp => by
    have h : p % q = a % q := (hP p hp).2.1
    rw [← h, Nat.div_add_mod]
  have hinj : Set.InjOn (fun p => p / q + 1) (P : Set ℕ) := by
    intro p hp p' hp' h
    have h' : p / q = p' / q := by simpa using h
    rw [hdec p hp, hdec p' hp', h']
  have key := GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime M N Q q (P.image fun p => p / q + 1) hQ hq ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at key
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨-, -, -, h1, h2⟩ := hP p hp
    have h3 : M ≤ p / q := (Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm])
    have h4 : p / q < M + N := (Nat.div_lt_iff_lt_mul hq).2 (by rwa [mul_comm])
    exact Finset.mem_Ioc.2 ⟨by omega, by omega⟩
  · intro l hl hlQ hlq
    obtain ⟨c, hc⟩ := exists_dvd_mul_add_of_prime l q (a % q) hl hlq
    refine ⟨c + 1, fun n hn h => ?_⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    have h1 : p / q ≡ c [MOD l] := Nat.ModEq.add_right_cancel' 1 h
    have h2 : q * (p / q) + a % q ≡ q * c + a % q [MOD l] := (h1.mul_left q).add_right _
    rw [← hdec p hp] at h2
    have h3 : l ∣ p := (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 hc))
    have h4 := (Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).1 h3
    have := (hP p hp).2.2.1
    omega

/- English proof (translation)
Use `⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩` and prove the remaining obligations. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hq`. Take `⟨z, hz⟩ : ∃ z : ℝ, z = y / q` from `⟨_, rfl⟩`. Establish `hyz : y = q * z` using `by rw [hz]; field_simp`. Establish `hz2 : 2 ≤ z` using `by rw [hz, le_div_iff₀ hq0]; exact hy`.

Rewrite using `[← hz]`. Establish `hfl : 2 ≤ ⌊z⌋₊` using `Nat.le_floor (by exact_mod_cast hz2)`. Establish `hflz : (⌊z⌋₊ : ℝ) ≤ z` using `Nat.floor_le (by linarith)`. Establish `hzfl : z < ⌊z⌋₊ + 1` using `Nat.lt_floor_add_one z`. Take `⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊` from `⟨_, rfl⟩`.

Establish `hs1 : 1 ≤ s` using `by rw [hs, Nat.le_sqrt]; omega`. Establish `hs2 : s * s ≤ ⌊z⌋₊` using `hs ▸ Nat.sqrt_le _`. Establish `hs3 : ⌊z⌋₊ < (s + 1) * (s + 1)` using `hs ▸ Nat.lt_succ_sqrt _`. Take `⟨Q, hQ⟩ : ∃ Q, Q = s + 1` from `⟨_, rfl⟩`. Establish `hQ2 : (2 : ℝ) ≤ Q` using `by exact_mod_cast (by omega : 2 ≤ Q)`.

Establish `hQz : (Q : ℝ) ^ 2 ≤ 4 * z`. Establish `: Q ^ 2 ≤ 4 * ⌊z⌋₊` using `by rw [hQ]; nlinarith`. Establish `: (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzQ : z ≤ (Q : ℝ) ^ 2`.

Establish `: ⌊z⌋₊ + 1 ≤ Q ^ 2` using `by rw [hQ]; nlinarith`. Establish `: (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlz : 0 < Real.log z` using `Real.log_pos (by linarith)`. Establish `hlog : Real.log z ≤ 2 * Real.log Q`.

Use `Real.log_le_log (by linarith) hzQ` as an intermediate fact. Rewrite `this` using `[Real.log_pow]`. Conclude with `this` after adjusting the coercions. Establish `hlQ : Real.log Q ≤ Q`. Use `Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hφ0 : (0 : ℝ) < q.totient` using `by exact_mod_cast Nat.totient_pos.2 hq`. Establish `hφq : (q.totient : ℝ) ≤ q` using `by exact_mod_cast Nat.totient_le q`. Use `set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP`. Establish `hbig` using `card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by`.

Introduce `p hp`. Simplify using `only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp`. Take `⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩` from `hp`. Use `⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩` and prove the remaining obligations. Establish `h6 : (p : ℝ) ≤ x + y` using `(Nat.le_floor_iff (by nlinarith)).1 h2`.

Establish `h7 : x < ⌊x⌋₊ + 1` using `Nat.lt_floor_add_one x`. Establish `h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1)` using `Nat.lt_mul_div_succ _ hq`. Establish `h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1)` using `by exact_mod_cast h8`. Establish `h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2))` using `by nlinarith`. Conclude with `h10)` after adjusting the coercions.

Establish `hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp`. Conclude with `Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩`. Use `_ = Q := by simp`.

Establish `hsum` using `Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)`. Take `⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ)` from `⟨_, rfl⟩`. Establish `hB0 : 0 ≤ B` using `hB ▸ Nat.cast_nonneg _`. Establish `hcard : (P.card : ℝ) ≤ B + Q`. Rewrite using `[hB]; exact_mod_cast (by omega)`.

Rewrite `hbig` using `[← hB]`. Move the coercions through the operations in `at hbig`. Establish `hpi` using `Real.pi_lt_four`. Establish `hpi0` using `Real.pi_pos`. Establish `h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z` using `by nlinarith`.

Establish `h2 : B * (q.totient * Real.log Q) ≤ 20 * y`. Use `mul_le_mul_of_nonneg_left h1 hq0.le` as an intermediate fact. Rewrite using `[hyz]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : B * (q.totient * Real.log z) ≤ 40 * y`.

Use `mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : (Q : ℝ) * Real.log z ≤ 8 * z` using `by nlinarith`. Establish `h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y`. Establish `: (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z)` using `mul_le_mul hφq h4 (by positivity) hq0.le`.

Rewrite using `[hyz]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[le_div_iff₀ (by positivity)]`. Use `mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  refine ⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = y / q := ⟨_, rfl⟩
  have hyz : y = q * z := by rw [hz]; field_simp
  have hz2 : 2 ≤ z := by rw [hz, le_div_iff₀ hq0]; exact hy
  rw [← hz]
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hflz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzfl : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hs2 : s * s ≤ ⌊z⌋₊ := hs ▸ Nat.sqrt_le _
  have hs3 : ⌊z⌋₊ < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s + 1 := ⟨_, rfl⟩
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (by omega : 2 ≤ Q)
  have hQz : (Q : ℝ) ^ 2 ≤ 4 * z := by
    have : Q ^ 2 ≤ 4 * ⌊z⌋₊ := by rw [hQ]; nlinarith
    have : (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊ := by exact_mod_cast this
    linarith
  have hzQ : z ≤ (Q : ℝ) ^ 2 := by
    have : ⌊z⌋₊ + 1 ≤ Q ^ 2 := by rw [hQ]; nlinarith
    have : (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ 2 * Real.log Q := by
    have := Real.log_le_log (by linarith) hzQ
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hlQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)
    linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP
  have hbig := card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by
    intro p hp
    simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩
    have h6 : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by nlinarith)).1 h2
    have h7 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1) := Nat.lt_mul_div_succ _ hq
    have h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1) := by exact_mod_cast h8
    have h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2)) := by nlinarith
    exact_mod_cast h10)
  have hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q := by
    calc _ ≤ (Finset.Icc 1 Q).card := Finset.card_le_card fun p hp => by
            simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
            exact Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩
      _ = Q := by simp
  have hsum := Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Nat.cast_nonneg _
  have hcard : (P.card : ℝ) ≤ B + Q := by
    rw [hB]; exact_mod_cast (by omega)
  rw [← hB] at hbig
  push_cast at hbig
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z := by nlinarith
  have h2 : B * (q.totient * Real.log Q) ≤ 20 * y := by
    have := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [hyz]
    calc _ = q * (B * ((q.totient : ℝ) / q * Real.log Q)) := by field_simp
      _ ≤ _ := by linarith
  have h3 : B * (q.totient * Real.log z) ≤ 40 * y := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)
    nlinarith
  have h4 : (Q : ℝ) * Real.log z ≤ 8 * z := by nlinarith
  have h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y := by
    have : (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z) :=
      mul_le_mul hφq h4 (by positivity) hq0.le
    rw [hyz]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)
  nlinarith

end GlobalTheory.Lin
