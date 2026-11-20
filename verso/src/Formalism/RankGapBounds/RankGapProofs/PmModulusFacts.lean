import Formalism.RankGapBounds.RandomSubsetCounterexample

namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

/- English proof (authored)
A natural number maps to zero in the residue ring modulo M precisely when it is divisible by M. Apply the forward implication.
-/
private theorem dvd_of_natCast_zmod_eq_zero {M a : ℕ} (h : (a : ZMod M) = 0) : M ∣ a := by
  exact (CharP.cast_eq_zero_iff (ZMod M) M a).mp h

/- English proof (authored)
Take l in s. If its residue is one, write l − 1 = qM. If its residue is minus one, write l + 1 = qM. In each case q ≥ 1 since l ≥ 3, and q − 1 < N since l ≤ N and M ≥ 2. Thus l occurs in the corresponding image at index q − 1.
-/
lemma pm_cover (M N : ℕ) (hM : 2 ≤ M) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1)) :
    s ⊆ (range N).image (fun k => (k + 1) * M + 1) ∪
      (range N).image (fun k => (k + 1) * M - 1) := by
  intro l hl
  obtain ⟨h3, hN, h⟩ := hs l hl
  simp only [mem_union, mem_image, mem_range]
  rcases h with h | h
  · left
    have hd : M ∣ l - 1 := dvd_of_natCast_zmod_eq_zero
      (by rw [Nat.cast_sub (by omega), Nat.cast_one, h, sub_self])
    obtain ⟨q, hq⟩ := hd
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have hqM : q ≤ M * q := by nlinarith
    refine ⟨q - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hq0, mul_comm]
    omega
  · right
    have hd : M ∣ l + 1 := dvd_of_natCast_zmod_eq_zero (by push_cast; rw [h]; ring)
    obtain ⟨q, hq⟩ := hd
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; omega
      · exact h0
    have h2q : 2 * q ≤ M * q := by nlinarith
    refine ⟨q - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel hq0, mul_comm]
    omega

/- English proof (authored)
The two progressions cover s. The summands are nonnegative, so the sum over s is at most the sum over the union, which in turn is at most the sum of the two separate sums. Each progression is injective in its index because M is positive, so these sums can be indexed by the indicated range.
-/
lemma pm_sum_cover (f : ℕ → ℝ) (hf : ∀ l, 0 ≤ f l) (M N : ℕ) (hM : 2 ≤ M) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1)) :
    ∑ l ∈ s, f l ≤
      ∑ k ∈ range N, f ((k + 1) * M + 1) + ∑ k ∈ range N, f ((k + 1) * M - 1) := by
  have hMpos : 0 < M := by omega
  have hsub := pm_cover M N hM s hs
  have hinj1 : Set.InjOn (fun k : ℕ => (k + 1) * M + 1) ((range N : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    have hab' : (a + 1) * M + 1 = (b + 1) * M + 1 := hab
    have h' : (a + 1) * M = (b + 1) * M := by omega
    have := Nat.eq_of_mul_eq_mul_right hMpos h'
    omega
  have hinj2 : Set.InjOn (fun k : ℕ => (k + 1) * M - 1) ((range N : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    have hab' : (a + 1) * M - 1 = (b + 1) * M - 1 := hab
    have ha : 0 < (a + 1) * M := Nat.mul_pos (Nat.succ_pos a) hMpos
    have hb : 0 < (b + 1) * M := Nat.mul_pos (Nat.succ_pos b) hMpos
    have h' : (a + 1) * M = (b + 1) * M := by omega
    have := Nat.eq_of_mul_eq_mul_right hMpos h'
    omega
  set A := (range N).image (fun k => (k + 1) * M + 1) with hA
  set B := (range N).image (fun k => (k + 1) * M - 1) with hB
  have hU : ∑ x ∈ A ∪ B, f x + ∑ x ∈ A ∩ B, f x = ∑ x ∈ A, f x + ∑ x ∈ B, f x :=
    Finset.sum_union_inter
  have hI0 : 0 ≤ ∑ x ∈ A ∩ B, f x := sum_nonneg (fun i _ => hf i)
  have hsA : ∑ x ∈ A, f x = ∑ k ∈ range N, f ((k + 1) * M + 1) := sum_image hinj1
  have hsB : ∑ x ∈ B, f x = ∑ k ∈ range N, f ((k + 1) * M - 1) := sum_image hinj2
  have hs1 : ∑ l ∈ s, f l ≤ ∑ x ∈ A ∪ B, f x :=
    sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
  linarith

/- English proof (authored)
Since 0 < a ≤ b, both numbers are in the interval where the logarithm is increasing.
-/
private theorem log_le_log_of_pos_of_le {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : Real.log a ≤ Real.log b := by
  exact Real.log_le_log ha h

/- English proof (authored)
Multiply the desired inequality by the positive product bd. The resulting inequality is precisely ad ≤ cb.
-/
private theorem div_le_div_of_mul_le_mul_of_pos' {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  first
  | exact (div_le_div_iff_of_pos hb hd).mpr h
  | exact (div_le_div_iff hb hd).mpr h
  | exact (div_le_div_iff₀ hb hd).mpr h

/- English proof (authored)
Since 1 ≤ m ≤ Y, one has 0 ≤ log m ≤ log Y. Also m ≥ xy/2 > 0, so 1/m ≤ 2/(xy). Multiplying the two bounds gives the result.
-/
lemma pm_key_Y (m x y Y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (h1 : x * y / 2 ≤ m) (hmY : m ≤ Y)
    (hm1 : 1 ≤ m) : Real.log m / m ≤ Real.log Y * (2 / y) * (1 / x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hm0 : 0 < m := by linarith
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hlmY : Real.log m ≤ Real.log Y := log_le_log_of_pos_of_le hm0 hmY
  have hlY : 0 ≤ Real.log Y := le_trans hlm hlmY
  rw [show Real.log Y * (2 / y) * (1 / x) = 2 * Real.log Y / (x * y) by ring]
  apply div_le_div_of_mul_le_mul_of_pos' hm0 (mul_pos hx0 hy0)
  nlinarith [mul_le_mul_of_nonneg_right hlmY (mul_pos hx0 hy0).le,
    mul_le_mul_of_nonneg_left h1 hlY]

noncomputable def pmW (k : ℕ) : ℝ := (1 + Real.log ((k : ℝ) + 1)) / ((k : ℝ) + 1) ^ 2

/- English proof (authored)
A multiple of M has residue zero in the residue ring modulo M.
-/
private theorem natCast_zmod_eq_zero_of_dvd {M a : ℕ} (h : M ∣ a) : (a : ZMod M) = 0 := by
  exact (CharP.cast_eq_zero_iff (ZMod M) M a).mpr h

/- English proof (authored)
Since k = 2, the modulus is four. An odd integer has remainder one or three modulo four, and three is the residue of minus one.
-/
private theorem natCast_zmod_four_eq_one_or_neg_one_of_odd (l k : ℕ) (hk : k = 2) (hodd : l % 2 = 1) :
    (l : ZMod (2 ^ k)) = 1 ∨ (l : ZMod (2 ^ k)) = -1 := by
  subst hk
  rcases (show l % 4 = 1 ∨ l % 4 = 3 by omega) with h | h
  · left
    have hd : 2 ^ 2 ∣ l - 1 := by show 4 ∣ l - 1; omega
    have h0 := natCast_zmod_eq_zero_of_dvd hd
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h0
    exact h0
  · right
    have hd : 2 ^ 2 ∣ l + 1 := by show 4 ∣ l + 1; omega
    have h0 := natCast_zmod_eq_zero_of_dvd hd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0

/- English proof (authored)
The odd residue of l is one or minus one modulo four. The order criterion at exponent e gives a power equal to the identity, so the order is 2ⁱ with i ≤ e. Its bound by J also gives i ≤ ⌊log₂ J⌋. For j equal to the minimum of these two bounds, the order divides 2ʲ. Apply the order criterion at j to deduce the asserted congruence.
-/
lemma pm_resid (hI : OrdersIff) (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) (hodd : l % 2 = 1)
    (hord : orderOf (hOf e l hl) ≤ J) :
    (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = 1 ∨
      (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = -1 := by
  have h4 := natCast_zmod_four_eq_one_or_neg_one_of_odd l (e + 2 - e) (by omega) hodd
  have hpow : (hOf e l hl) ^ (2 ^ e) = 1 := (hI e e l hl le_rfl).mpr h4
  have hdvd : orderOf (hOf e l hl) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hiJ : 2 ^ i ≤ J := by rw [← hoi]; exact hord
  have hJ0 : J ≠ 0 := by
    have : 0 < 2 ^ i := by positivity
    omega
  have hilog : i ≤ Nat.log 2 J := by
    exact Nat.le_log_of_pow_le (by norm_num) hiJ
  have hij : i ≤ min e (Nat.log 2 J) := le_min hi hilog
  apply (hI e (min e (Nat.log 2 J)) l hl (min_le_left _ _)).mp
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hoi]
  exact pow_dvd_pow 2 hij

/- English proof (authored)
For a positive natural number n, n ≥ 1 and its logarithm is nonnegative. At zero the real-logarithm convention gives zero.
-/
private theorem log_natCast_nonneg_real (n : ℕ) : 0 ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Real.log_nonneg (Nat.one_le_cast.mpr h)

/- English proof (authored)
The empty sum and the sum with one term satisfy the estimate directly. For positive n, the inequality log(n/(n + 1)) ≤ n/(n + 1) − 1 gives 1/(n + 1) ≤ log(n + 1) − log n. Adding that bound at each step proves the harmonic estimate by induction.
-/
private theorem sum_range_inv_succ_le_one_add_log (N : ℕ) :
    ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hstep : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / (n + 1) by positivity)
        rw [Real.log_div hn'.ne' (by positivity)] at h
        have h' : (n : ℝ) / (n + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
          field_simp
          ring
        linarith
      push_cast
      linarith

/- English proof (authored)
Use the nonnegative weight log l/l for l ≤ Y and zero beyond Y. The progression cover bounds the sum over s by the sums on the two progressions. On either progression, m = (k + 1)M ± 1 is at least (k + 1)M/2. Each weight is therefore at most 2 log Y divided by M(k + 1). Apply the harmonic bound in each progression and use N ≤ Y.
-/
lemma pm_y_sum (M N : ℕ) (hM : 2 ≤ M) (Y : ℝ) (hY : 1 ≤ Y) (hNY : (N : ℝ) ≤ Y) (s : Finset ℕ)
    (hs : ∀ l ∈ s, 3 ≤ l ∧ l ≤ N ∧ ((l : ZMod M) = 1 ∨ (l : ZMod M) = -1))
    (hsY : ∀ l ∈ s, (l : ℝ) ≤ Y) :
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ 4 * Real.log Y * (1 + Real.log Y) / M := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  set f : ℕ → ℝ := fun l => if (l : ℝ) ≤ Y then Real.log l / (l : ℝ) else 0 with hfdef
  have hf0 : ∀ l, 0 ≤ f l := by
    intro l
    simp only [hfdef]
    split_ifs
    · exact div_nonneg (log_natCast_nonneg_real l) (Nat.cast_nonneg l)
    · exact le_rfl
  have hsf : ∑ l ∈ s, Real.log l / (l : ℝ) = ∑ l ∈ s, f l := by
    apply sum_congr rfl
    intro l hl
    simp only [hfdef]
    rw [if_pos (hsY l hl)]
  have hmain := pm_sum_cover f hf0 M N hM s hs
  have hterm : ∀ k m : ℕ, ((k : ℝ) + 1) * M / 2 ≤ m → 1 ≤ m →
      f m ≤ Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    intro k m h1 hm1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hnn : 0 ≤ Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) :=
      mul_nonneg (mul_nonneg hlY (by positivity)) (by positivity)
    simp only [hfdef]
    split_ifs with hmY
    · exact pm_key_Y m ((k : ℝ) + 1) M Y hk1 (by linarith) h1 hmY
        (by exact_mod_cast hm1)
    · exact hnn
  have hsumk : ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) ≤
      2 * Real.log Y * (1 + Real.log Y) / M := by
    rw [← mul_sum]
    have hH := sum_range_inv_succ_le_one_add_log N
    have hNl : 1 + Real.log N ≤ 1 + Real.log Y := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
      · have : (0 : ℝ) < N := by exact_mod_cast h0
        have := log_le_log_of_pos_of_le this hNY
        linarith
    calc Real.log Y * (2 / M) * ∑ k ∈ range N, 1 / ((k : ℝ) + 1)
        ≤ Real.log Y * (2 / M) * (1 + Real.log Y) :=
          mul_le_mul_of_nonneg_left (hH.trans hNl) (mul_nonneg hlY (by positivity))
      _ = 2 * Real.log Y * (1 + Real.log Y) / M := by ring
  have hA : ∑ k ∈ range N, f ((k + 1) * M + 1) ≤
      ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    apply sum_le_sum
    intro k _
    apply hterm k
    · have hkM : (0 : ℝ) ≤ (k : ℝ) * M := mul_nonneg (Nat.cast_nonneg k) hM0.le
      push_cast
      nlinarith
    · omega
  have hB : ∑ k ∈ range N, f ((k + 1) * M - 1) ≤
      ∑ k ∈ range N, Real.log Y * (2 / M) * (1 / ((k : ℝ) + 1)) := by
    apply sum_le_sum
    intro k _
    have h1le : 1 * M ≤ (k + 1) * M := Nat.mul_le_mul (by omega) (le_refl M)
    apply hterm k
    · have hkM : (0 : ℝ) ≤ (k : ℝ) * M := mul_nonneg (Nat.cast_nonneg k) hM0.le
      rw [Nat.cast_sub (by omega)]
      push_cast
      nlinarith
    · omega
  calc ∑ l ∈ s, Real.log l / (l : ℝ) = ∑ l ∈ s, f l := hsf
    _ ≤ _ := hmain
    _ ≤ 2 * Real.log Y * (1 + Real.log Y) / M + 2 * Real.log Y * (1 + Real.log Y) / M :=
        add_le_add (hA.trans hsumk) (hB.trans hsumk)
    _ = 4 * Real.log Y * (1 + Real.log Y) / M := by ring

/- English proof (authored)
Write j = min(e, ⌊log₂ J⌋). Since j ≤ e, the exponent e + 2 − j lies between two and e + 2. Also 2ʲ ≤ J. Hence 2ᵉ = 2ʲ times 2 raised to e − j, which is bounded by J times 2 raised to e + 2 − j.
-/
lemma pm_modulus_facts (e J : ℕ) (hJ : 1 ≤ J) :
    2 ≤ 2 ^ (e + 2 - min e (Nat.log 2 J)) ∧ 2 ^ (e + 2 - min e (Nat.log 2 J)) ≤ 2 ^ (e + 2) ∧
      2 ^ e ≤ J * 2 ^ (e + 2 - min e (Nat.log 2 J)) := by
  have hje : min e (Nat.log 2 J) ≤ e := min_le_left _ _
  have hjl : min e (Nat.log 2 J) ≤ Nat.log 2 J := min_le_right _ _
  have h2j : 2 ^ min e (Nat.log 2 J) ≤ J :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjl) (Nat.pow_log_le_self 2 (by omega))
  refine ⟨?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (e + 2 - min e (Nat.log 2 J)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · calc 2 ^ e = 2 ^ min e (Nat.log 2 J) * 2 ^ (e - min e (Nat.log 2 J)) := by
          rw [← pow_add, Nat.add_sub_of_le hje]
      _ ≤ J * 2 ^ (e + 2 - min e (Nat.log 2 J)) :=
          Nat.mul_le_mul h2j (Nat.pow_le_pow_right (by norm_num) (by omega))

/- English proof (authored)
Use the inequality log x ≥ 1 − 1/x for positive x and set x = 2.
-/
private theorem one_half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  linarith

/- English proof (authored)
Choose M = 2 raised to e + 2 minus min(e, ⌊log₂ J⌋). The order bound places every prime in the sum in one of the two classes ±1 modulo M. The progression estimate bounds the sum by 4 log Y(1 + log Y)/M, and the modulus estimate gives 1/M ≤ J/2ᵉ. Since e ≥ 1, e log 2 ≥ 1/2. Expanding the square of e log 2 + log Y shows that three times this square bounds log Y(1 + log Y). This gives the claimed constant twelve.
-/
theorem ordersSumY_of (hI : OrdersIff) : OrdersSumY := by
  refine ⟨12, ?_⟩
  intro e J Y s he hJ hY hs
  obtain ⟨hM2, -, hJM⟩ := pm_modulus_facts e J hJ
  have hY0 : 0 ≤ Y := by linarith
  have hs' : ∀ l ∈ s, 3 ≤ l ∧ l ≤ ⌊Y⌋₊ ∧
      ((l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = 1 ∨
        (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = -1) := by
    intro l hl
    obtain ⟨hp, h2, hlY, hl', hord⟩ := hs l hl
    have hodd : l % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
    have h3 : 3 ≤ l := by have := hp.two_le; omega
    exact ⟨h3, Nat.le_floor hlY, pm_resid hI e J l hl' hodd hord⟩
  have hsum := pm_y_sum _ ⌊Y⌋₊ hM2 Y hY (Nat.floor_le hY0) s hs'
    (fun l hl => (hs l hl).2.2.1)
  set M : ℕ := 2 ^ (e + 2 - min e (Nat.log 2 J)) with hMdef
  have hm2 : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hm0 : (0 : ℝ) < M := by linarith
  have hP : (2 : ℝ) ^ e ≤ (J : ℝ) * M := by exact_mod_cast hJM
  have hlY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hL := one_half_le_log_two
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hΛ : Real.log ((2 : ℝ) ^ e * Y) = e * Real.log 2 + Real.log Y := by
    rw [Real.log_mul (by positivity) (show (0 : ℝ) < Y by linarith).ne', Real.log_pow]
  have hΛ1 : 1 / 2 ≤ (e : ℝ) * Real.log 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ e - 1) (by linarith : (0 : ℝ) ≤ Real.log 2)]
  have hkey : Real.log Y * (1 + Real.log Y) ≤ 3 * Real.log ((2 : ℝ) ^ e * Y) ^ 2 := by
    rw [hΛ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hΛ1) hlY, sq_nonneg ((e : ℝ) * Real.log 2),
      sq_nonneg (Real.log Y)]
  have hPpos : (0 : ℝ) < 2 ^ e := by positivity
  calc ∑ l ∈ s, Real.log l / (l : ℝ) ≤ 4 * Real.log Y * (1 + Real.log Y) / M := hsum
    _ ≤ 12 * (J : ℝ) * Real.log ((2 : ℝ) ^ e * Y) ^ 2 / (2 : ℝ) ^ e := by
      apply div_le_div_of_mul_le_mul_of_pos' hm0 hPpos
      nlinarith [mul_nonneg (sub_nonneg.mpr hkey) hPpos.le,
        mul_nonneg (sq_nonneg (Real.log ((2 : ℝ) ^ e * Y))) (sub_nonneg.mpr hP)]

end Formalism.RankGapBounds.LocalQuadraticParts
