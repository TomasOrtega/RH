import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LazardBinomialNormUltrametric
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.LazardOne

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `A B hB`. Establish `: B = 0` using `by simpa using hB`.

Substitute `this` using the available equality. Simplify using `[Nat.ModEq]`. Consider the case `succ s ih`. Introduce `A B hB`. Establish `h` using `@Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _`.

Establish `e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A)` using `by ring`. Rewrite `h` using `[e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self, one_mul]`. Establish `hB' : B / p < p ^ s`. Rewrite using `[Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]`. Conclude with `hB`.

Use `ih A (B / p) hB'` as an intermediate fact. Rewrite `this` using `[add_comm (p ^ s * A)]`. Rewrite using `[e0]`. Conclude with `h.trans this`.
-/
theorem choose_pow_mul_add_modEq_one (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → (p ^ s * A + B).choose B ≡ 1 [MOD p] := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this
    simp [Nat.ModEq]
  | succ s ih =>
    intro A B hB
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    have := ih A (B / p) hB'
    rw [add_comm (p ^ s * A)] at this
    rw [e0]; exact h.trans this

/- English proof (translation)
Introduce `hd`. Establish `h0` using `(Nat.modEq_zero_iff_dvd.2 hd).symm.trans (choose_pow_mul_add_modEq_one p s A B hB)`. Conclude with `hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.1 h0.symm)`.
-/
theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] (s A B : ℕ) (hB : B < p ^ s) :
    ¬ p ∣ (p ^ s * A + B).choose B := by
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans (choose_pow_mul_add_modEq_one p s A B hB)
  exact hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.1 h0.symm)

variable (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

/- English proof (translation)
Establish `hA : ∀ i n, c i = 0 → 0 < i → i < n → n < N → ¬ p ∣ n.choose i → c n = 0`. Introduce `i n hi hi0 hin hnN hd`. Establish `h` using `hrel i (n - i) (N - n) hi0 (by omega) (by omega) (by omega)`. Rewrite `h` using `[show i + (n - i) = n by omega, hi, zero_mul]`. Establish `hne : ((n.choose i : ℕ) : k) ≠ 0`.

Rewrite using `[Ne, CharP.cast_eq_zero_iff k p]`. Conclude with `hd`. Conclude with `(mul_eq_zero.1 h).resolve_right hne`. Establish `hq : 0 < p ^ s` using `pow_pos hp.out.pos s`. Establish `hb1 : ∀ u, 0 < u → u < K → ¬ p ∣ u → c (p ^ s * u) = 0`.

Introduce `u hu huK hpu`. Break down `Nat.lt_or_ge 1 u with h1 | h1` into its components or cases. Use `hA (p ^ s) (p ^ s * u) h0 hq (lt_mul_of_one_lt_right hq h1) ?_ (GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp.out u hpu s)` and prove the remaining obligations. Rewrite using `[hN]`. Conclude with `Nat.mul_lt_mul_of_pos_left huK hq`.

Establish `: u = 1` using `by omega`. Substitute `this` using the available equality. Simplify using `using h0`. Establish `hb : ∀ u, 0 < u → u < K → c (p ^ s * u) = 0`. Introduce `u hu huK`.

Break down `hK u hu huK with h | h` into its components or cases. Conclude with `hb1 u hu huK h`. Establish `h'` using `hb1 (K - u) (by omega) (by omega) h`. Establish `hle : p ^ s * (K - u) ≤ N` using `by rw [hN]; exact Nat.mul_le_mul_left _ (by omega)`. Rewrite `h'` using `[hsym _ hle]`.

Rewrite using `[show N - p ^ s * (K - u) = p ^ s * u by` and apply the resulting hypothesis. Rewrite using `[hN, ← Nat.mul_sub]`. Use `congr 1`. Use the proof step `omega] at h'`. Introduce `n hn hnN`.

Take `⟨u, v, hvlt, rfl⟩ : ∃ u v, v < p ^ s ∧ n = p ^ s * u + v` from `⟨n / p ^ s, n % p ^ s, Nat.mod_lt _ hq, (Nat.div_add_mod n (p ^ s)).symm⟩`. Establish `huK : u < K`. Apply `Nat.lt_of_mul_lt_mul_left (a := p ^ s)` to reduce the goal to its premises. Rewrite using `[← hN]`. Use linear arithmetic over natural numbers and integers.

Break down `Nat.eq_zero_or_pos v with hv | hv` into its components or cases. Substitute `hv` using the available equality. Rewrite `hn`, the goal using `[add_zero]`. Break down `Nat.eq_zero_or_pos u with hu | hu` into its components or cases. Substitute `hu` using the available equality.

Simplify using `at hn`. Conclude with `hb u hu huK`. Establish `hK1 : c (p ^ s * (K - 1)) = 0` using `hb (K - 1) (by omega) (by omega)`. Establish `e1 : p ^ s * K = p ^ s * (K - 1) + p ^ s`. Rewrite using `[← Nat.mul_succ]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Establish `hNv : N - v = p ^ s * (K - 1) + (p ^ s - v)` using `by omega`. Establish `hpos : 0 < p ^ s * (K - 1)` using `Nat.mul_pos hq (by omega)`. Establish `hcNv : c (N - v) = 0`.

Rewrite using `[hNv]`. Use `hA (p ^ s * (K - 1)) _ hK1 hpos (by omega) (by omega) ?_` and prove the remaining obligations. Rewrite using `[Nat.choose_symm_add]`. Conclude with `not_dvd_choose_pow_mul_add p s (K - 1) (p ^ s - v) (by omega)`. Establish `hcv : c v = 0` using `by rw [hsym v (by omega), hcNv]`.

Break down `Nat.eq_zero_or_pos u with hu | hu` into its components or cases. Substitute `hu` using the available equality. Simplify using `using hcv`. Establish `hsu : 0 < p ^ s * u` using `Nat.mul_pos hq hu`. Conclude with `hA v _ hcv hv (by omega) hnN (not_dvd_choose_pow_mul_add p s u v hvlt)`.
-/
theorem eq_zero_of_eq_zero (N : ℕ) (c : ℕ → k)
    (hsym : ∀ i, i ≤ N → c i = c (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      c (i + j) * ((i + j).choose i : k) = c i * ((j + l).choose j : k))
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (h0 : c (p ^ s) = 0) : ∀ n, 0 < n → n < N → c n = 0 := by
  have hA : ∀ i n, c i = 0 → 0 < i → i < n → n < N → ¬ p ∣ n.choose i → c n = 0 := by
    intro i n hi hi0 hin hnN hd
    have h := hrel i (n - i) (N - n) hi0 (by omega) (by omega) (by omega)
    rw [show i + (n - i) = n by omega, hi, zero_mul] at h
    have hne : ((n.choose i : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]; exact hd
    exact (mul_eq_zero.1 h).resolve_right hne
  have hq : 0 < p ^ s := pow_pos hp.out.pos s
  have hb1 : ∀ u, 0 < u → u < K → ¬ p ∣ u → c (p ^ s * u) = 0 := by
    intro u hu huK hpu
    rcases Nat.lt_or_ge 1 u with h1 | h1
    · refine hA (p ^ s) (p ^ s * u) h0 hq (lt_mul_of_one_lt_right hq h1) ?_
        (GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp.out u hpu s)
      rw [hN]; exact Nat.mul_lt_mul_of_pos_left huK hq
    · have : u = 1 := by omega
      subst this; simpa using h0
  have hb : ∀ u, 0 < u → u < K → c (p ^ s * u) = 0 := by
    intro u hu huK
    rcases hK u hu huK with h | h
    · exact hb1 u hu huK h
    · have h' := hb1 (K - u) (by omega) (by omega) h
      have hle : p ^ s * (K - u) ≤ N := by rw [hN]; exact Nat.mul_le_mul_left _ (by omega)
      rw [hsym _ hle] at h'
      rwa [show N - p ^ s * (K - u) = p ^ s * u by
        rw [hN, ← Nat.mul_sub]; congr 1; omega] at h'
  intro n hn hnN
  obtain ⟨u, v, hvlt, rfl⟩ : ∃ u v, v < p ^ s ∧ n = p ^ s * u + v :=
    ⟨n / p ^ s, n % p ^ s, Nat.mod_lt _ hq, (Nat.div_add_mod n (p ^ s)).symm⟩
  have huK : u < K := by
    apply Nat.lt_of_mul_lt_mul_left (a := p ^ s)
    rw [← hN]; omega
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    rw [add_zero] at hn ⊢
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simp at hn
    · exact hb u hu huK
  · have hK1 : c (p ^ s * (K - 1)) = 0 := hb (K - 1) (by omega) (by omega)
    have e1 : p ^ s * K = p ^ s * (K - 1) + p ^ s := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hNv : N - v = p ^ s * (K - 1) + (p ^ s - v) := by omega
    have hpos : 0 < p ^ s * (K - 1) := Nat.mul_pos hq (by omega)
    have hcNv : c (N - v) = 0 := by
      rw [hNv]
      refine hA (p ^ s * (K - 1)) _ hK1 hpos (by omega) (by omega) ?_
      rw [Nat.choose_symm_add]
      exact not_dvd_choose_pow_mul_add p s (K - 1) (p ^ s - v) (by omega)
    have hcv : c v = 0 := by rw [hsym v (by omega), hcNv]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simpa using hcv
    · have hsu : 0 < p ^ s * u := Nat.mul_pos hq hu
      exact hA v _ hcv hv (by omega) hnN (not_dvd_choose_pow_mul_add p s u v hvlt)

/- English proof (translation)
Use `set b : ℕ → k := fun i => ((N.choose i / g : ℕ) : k) with hbdef`. Establish `hbsym : ∀ i, i ≤ N → b (N - i) = b i`. Introduce `i hi`. Simplify using `only [hbdef, Nat.choose_symm hi]`. Establish `hbrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → b (i + j) * ((i + j).choose i : k) = b i * ((j + l).choose j : k)`.

Introduce `i j l hi hj hl hs`. Take `⟨x, hx⟩` from `hdiv (i + j) (by omega) (by omega)`. Take `⟨y, hy⟩` from `hdiv i hi (by omega)`. Establish `hm` using `Nat.choose_mul (n := N) (k := i + j) (s := i) (by omega)`. Rewrite `hm` using `[show N - i = j + l by omega, show i + j - i = j by omega, hx, hy, mul_assoc, mul_assoc]`.

Establish `hm'` using `Nat.eq_of_mul_eq_mul_left hg hm`. Simplify using `only [hbdef, hx, hy, Nat.mul_div_cancel_left _ hg]`. Rewrite using `[← Nat.cast_mul, ← Nat.cast_mul, hm']`. Use `⟨a (p ^ s) / b (p ^ s), ?_⟩` and prove the remaining obligations. Establish `key` using `eq_zero_of_eq_zero p N (fun i => a i - a (p ^ s) / b (p ^ s) * b i) ?_ ?_ s K hN hK2 hK ?_`.

Introduce `i hi hiN`. Conclude with `sub_eq_zero.1 (key i hi hiN)`. Introduce `i hi`. Rewrite using `[hsym i hi, hbsym i hi]`. Introduce `i j l hi hj hl hs`.

Rewrite using `[sub_mul, sub_mul, hrel i j l hi hj hl hs, mul_assoc, mul_assoc, hbrel i j l hi hj hl hs]`. Rewrite using `[div_mul_cancel₀ _ hb, sub_self]`.
-/
theorem exists_scalar (N : ℕ) (a : ℕ → k)
    (hsym : ∀ i, i ≤ N → a i = a (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k))
    (g : ℕ) (hg : 0 < g) (hdiv : ∀ i, 0 < i → i < N → g ∣ N.choose i)
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (hb : ((N.choose (p ^ s) / g : ℕ) : k) ≠ 0) :
    ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
  set b : ℕ → k := fun i => ((N.choose i / g : ℕ) : k) with hbdef
  have hbsym : ∀ i, i ≤ N → b (N - i) = b i := by
    intro i hi; simp only [hbdef, Nat.choose_symm hi]
  have hbrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      b (i + j) * ((i + j).choose i : k) = b i * ((j + l).choose j : k) := by
    intro i j l hi hj hl hs
    obtain ⟨x, hx⟩ := hdiv (i + j) (by omega) (by omega)
    obtain ⟨y, hy⟩ := hdiv i hi (by omega)
    have hm := Nat.choose_mul (n := N) (k := i + j) (s := i) (by omega)
    rw [show N - i = j + l by omega, show i + j - i = j by omega, hx, hy, mul_assoc, mul_assoc] at hm
    have hm' := Nat.eq_of_mul_eq_mul_left hg hm
    simp only [hbdef, hx, hy, Nat.mul_div_cancel_left _ hg]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hm']
  refine ⟨a (p ^ s) / b (p ^ s), ?_⟩
  have key := eq_zero_of_eq_zero p N (fun i => a i - a (p ^ s) / b (p ^ s) * b i) ?_ ?_ s K hN hK2 hK ?_
  · intro i hi hiN
    exact sub_eq_zero.1 (key i hi hiN)
  · intro i hi
    rw [hsym i hi, hbsym i hi]
  · intro i j l hi hj hl hs
    rw [sub_mul, sub_mul, hrel i j l hi hj hl hs, mul_assoc, mul_assoc, hbrel i j l hi hj hl hs]
  · rw [div_mul_cancel₀ _ hb, sub_self]

/- English proof (translation)
Introduce `p _ k _ _ _ N a hN2 hsym hrel`. Establish `hp : p.Prime` using `Fact.out`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg, hg1, hdiv, z, hz⟩ : ∃ g, 0 < g ∧ (g = 1 ∨ g = p) ∧ (∀ i, 0 < i → i < N → g ∣ N.choose i) ∧ ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by`. Take `⟨r, m, hm, hNe⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) p hp.one_lt.ne'`. Distinguish the cases in `hm1 : m = 1`.

Substitute `hm1` using the available equality. Rewrite `hNe` using `[mul_one]`. Establish `hr : 0 < r`. Break down `Nat.eq_zero_or_pos r with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `at hNe`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hdv : ∀ i, 0 < i → i < N → p ∣ N.choose i`. Introduce `i hi hiN; rw [hNe] at hiN ⊢; exact hp.dvd_choose_pow (by omega) (by omega)`.

Use `⟨p, hp.pos, Or.inr rfl, hdv, ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hch⟩` from `GlobalTheory.Honda.Lazard.choose_prime_pow_pred hp r hr`. Use `exists_scalar p N a hsym hrel p hp.pos hdv (r - 1) p ?_ hp.two_le ?_ ?_` and prove the remaining obligations. Rewrite using `[hNe, ← pow_succ]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Introduce `u hu hup; left; exact fun h => absurd (Nat.le_of_dvd hu h) (by omega)`. Rewrite using `[hNe, hch, Nat.mul_div_cancel_left _ hp.pos, Ne, CharP.cast_eq_zero_iff k p]`. Conclude with `hc`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hNe; omega`.

Establish `hm2 : 2 ≤ m` using `by omega`. Use `⟨1, one_pos, Or.inl rfl, fun _ _ _ => one_dvd _, ?_⟩` and prove the remaining obligations. Use `exists_scalar p N a hsym hrel 1 one_pos (fun _ _ _ => one_dvd _) r m hNe hm2 ?_ ?_` and prove the remaining obligations. Introduce `u hu huK`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Use `Nat.dvd_add h.2 h.1` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel huK.le]`. Conclude with `hm this`. Rewrite using `[Nat.div_one, hNe, Ne, CharP.cast_eq_zero_iff k p]`.

Conclude with `GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp m hm r`. Establish `hgW : ((g : ℕ) : WittVector p k) ≠ 0`. Break down `hg1 with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Introduce `h0`. Use `congrArg (fun x : WittVector p k => x.coeff 1) h0` as an intermediate fact. Simplify using `only [WittVector.coeff_p_one, WittVector.zero_coeff] at this`. Conclude with `one_ne_zero this`.

Establish `hgF : ((g : ℕ) : Fr p k) ≠ 0`. Rewrite using `[← map_natCast (algebraMap (WittVector p k) (Fr p k)), Ne, map_eq_zero_iff _ (IsFractionRing.injective (WittVector p k) (Fr p k))]`. Conclude with `hgW`. Use `⟨algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p z) / (g : Fr p k), ?_⟩` and prove the remaining obligations. Introduce `i hi hiN`.

Take `⟨q, hq⟩` from `hdiv i hi hiN`. Use `⟨WittVector.teichmuller p z * (q : WittVector p k), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, Nat.cast_mul, map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hz i hi hiN, hq, Nat.mul_div_cancel_left _ hg, map_mul, map_natCast, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`.
-/
theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ)
    (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) →
    (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) →
    ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k,
      t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧
      WittVector.constantCoeff w = a i := by
  intro p _ k _ _ _ N a hN2 hsym hrel
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg, hg1, hdiv, z, hz⟩ : ∃ g, 0 < g ∧ (g = 1 ∨ g = p) ∧
      (∀ i, 0 < i → i < N → g ∣ N.choose i) ∧
      ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
    obtain ⟨r, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) p hp.one_lt.ne'
    by_cases hm1 : m = 1
    · subst hm1
      rw [mul_one] at hNe
      have hr : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hNe; omega
        · exact h
      have hdv : ∀ i, 0 < i → i < N → p ∣ N.choose i := by
        intro i hi hiN; rw [hNe] at hiN ⊢; exact hp.dvd_choose_pow (by omega) (by omega)
      refine ⟨p, hp.pos, Or.inr rfl, hdv, ?_⟩
      obtain ⟨c, hc, hch⟩ := GlobalTheory.Honda.Lazard.choose_prime_pow_pred hp r hr
      refine exists_scalar p N a hsym hrel p hp.pos hdv (r - 1) p ?_ hp.two_le ?_ ?_
      · rw [hNe, ← pow_succ]; congr 1; omega
      · intro u hu hup; left; exact fun h => absurd (Nat.le_of_dvd hu h) (by omega)
      · rw [hNe, hch, Nat.mul_div_cancel_left _ hp.pos, Ne, CharP.cast_eq_zero_iff k p]; exact hc
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hNe; omega
      have hm2 : 2 ≤ m := by omega
      refine ⟨1, one_pos, Or.inl rfl, fun _ _ _ => one_dvd _, ?_⟩
      refine exists_scalar p N a hsym hrel 1 one_pos (fun _ _ _ => one_dvd _) r m hNe hm2 ?_ ?_
      · intro u hu huK
        by_contra h
        push_neg at h
        have := Nat.dvd_add h.2 h.1
        rw [Nat.sub_add_cancel huK.le] at this
        exact hm this
      · rw [Nat.div_one, hNe, Ne, CharP.cast_eq_zero_iff k p]
        exact GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp m hm r
  have hgW : ((g : ℕ) : WittVector p k) ≠ 0 := by
    rcases hg1 with h | h
    · subst h; simp
    · rw [h]
      intro h0
      have := congrArg (fun x : WittVector p k => x.coeff 1) h0
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
      exact one_ne_zero this
  have hgF : ((g : ℕ) : Fr p k) ≠ 0 := by
    rw [← map_natCast (algebraMap (WittVector p k) (Fr p k)), Ne,
      map_eq_zero_iff _ (IsFractionRing.injective (WittVector p k) (Fr p k))]
    exact hgW
  refine ⟨algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p z) / (g : Fr p k), ?_⟩
  intro i hi hiN
  obtain ⟨q, hq⟩ := hdiv i hi hiN
  refine ⟨WittVector.teichmuller p z * (q : WittVector p k), ?_, ?_⟩
  · rw [hq, Nat.cast_mul, map_mul, map_natCast]
    field_simp
  · rw [hz i hi hiN, hq, Nat.mul_div_cancel_left _ hg, map_mul, map_natCast,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.LazardOne
