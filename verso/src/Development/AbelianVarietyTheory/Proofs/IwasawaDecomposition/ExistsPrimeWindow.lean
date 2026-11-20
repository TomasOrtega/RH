import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween

noncomputable section
open Polynomial Formalism.CyclotomicNorms

namespace GlobalTheory.MemN.GoodEx

/- English proof (translation)
Distinguish the cases in `h : 100000 ≤ N`. Establish `h1` using `GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between N h`. Establish `h2 : (0 : ℝ) < 1 / (10 * Real.log N)`. Establish `: 0 < Real.log N` using `Real.log_pos (by exact_mod_cast (by omega : 1 < N))`. Check the signs of the components of the expression.

Take `⟨p, hp, -⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (h2.trans_le h1).ne'`. Conclude with `⟨p, (Finset.mem_filter.1 hp).2⟩`. Establish `key : ∀ p : ℕ, p.Prime → p + 3 ≤ N → (2 * p ≤ N → ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) → ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N`. Introduce `p hp h1 h2`. Distinguish the cases in `h3 : 2 * p ≤ N`.

Conclude with `h2 h3`. Conclude with `⟨p, hp, by omega, h1⟩`. Use `key 5 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 7 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 11 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations.

Use `key 19 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 31 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 59 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 113 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 223 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations.

Use `key 443 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 883 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 1759 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 3511 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 7019 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations.

Use `key 14033 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 28057 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use `key 56101 (by norm_num) (by omega) fun _ => ?_` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime_window (N : ℕ) (hN : 8 ≤ N) : ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N := by
  by_cases h : 100000 ≤ N
  · have h1 := GlobalTheory.BadShare.inv_log_le_sum_inv_primes_between N h
    have h2 : (0 : ℝ) < 1 / (10 * Real.log N) := by
      have : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      positivity
    obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2.trans_le h1).ne'
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  · have key : ∀ p : ℕ, p.Prime → p + 3 ≤ N → (2 * p ≤ N → ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) →
        ∃ p : ℕ, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N := by
      intro p hp h1 h2
      by_cases h3 : 2 * p ≤ N
      · exact h2 h3
      · exact ⟨p, hp, by omega, h1⟩
    refine key 5 (by norm_num) (by omega) fun _ => ?_
    refine key 7 (by norm_num) (by omega) fun _ => ?_
    refine key 11 (by norm_num) (by omega) fun _ => ?_
    refine key 19 (by norm_num) (by omega) fun _ => ?_
    refine key 31 (by norm_num) (by omega) fun _ => ?_
    refine key 59 (by norm_num) (by omega) fun _ => ?_
    refine key 113 (by norm_num) (by omega) fun _ => ?_
    refine key 223 (by norm_num) (by omega) fun _ => ?_
    refine key 443 (by norm_num) (by omega) fun _ => ?_
    refine key 883 (by norm_num) (by omega) fun _ => ?_
    refine key 1759 (by norm_num) (by omega) fun _ => ?_
    refine key 3511 (by norm_num) (by omega) fun _ => ?_
    refine key 7019 (by norm_num) (by omega) fun _ => ?_
    refine key 14033 (by norm_num) (by omega) fun _ => ?_
    refine key 28057 (by norm_num) (by omega) fun _ => ?_
    refine key 56101 (by norm_num) (by omega) fun _ => ?_
    omega

/- English proof (translation)
Use `⟨hl, ?_⟩` and prove the remaining obligations. Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨e, he⟩ : ∃ e, e = Nat.gcd d a` from `⟨_, rfl⟩`. Establish `h2 : g ^ d - 1 ∣ (g ^ e - 1) * l ^ s`. Rewrite using `[he, ← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_right]`.

Conclude with `Nat.dvd_gcd (Dvd.intro _ rfl) h`. Establish `hed : e ∣ d` using `he ▸ Nat.gcd_dvd_left d a`. Establish `hea : e ≤ a` using `he ▸ Nat.gcd_le_right d ha`. Establish `he0 : 0 < e` using `he ▸ Nat.gcd_pos_of_pos_right d ha`. Establish `h2e : 2 * e ≤ d`.

Take `⟨c, rfl⟩` from `hed`. Break down `c with _ | _ | c` into its components or cases. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨M, hM⟩ : g ^ e - 1 ∣ g ^ d - 1` from `Nat.pow_sub_one_dvd_pow_sub_one g hed`. Establish `hD : 1 < g ^ e` using `Nat.one_lt_pow he0.ne' (by omega)`. Establish `hd1 : 1 < g ^ d` using `Nat.one_lt_pow (by omega) (by omega)`. Rewrite `h2` using `[hM]`. Take `⟨t, -, rfl⟩` from `(Nat.dvd_prime_pow hl).1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2)`.

Establish `ht : t ≤ padicValNat l (g ^ d - 1)` using `(padicValNat_dvd_iff_le (by omega)).1 ⟨_, by rw [hM, mul_comm]⟩`. Establish `h3 : g ^ (d - e) ≤ l ^ t`. Establish `h4 : g ^ d = g ^ e * g ^ (d - e)` using `by rw [← pow_add]; congr 1; omega`. Establish `h5 : 1 ≤ l ^ t` using `Nat.one_le_pow _ _ hl.pos`. Establish `h6 : g ^ d ≤ g ^ e * l ^ t`.

Take `⟨A, hA⟩ : ∃ A, g ^ e = A + 1` from `⟨g ^ e - 1, by omega⟩`. Rewrite `hM`, the goal using `[hA]`. Rewrite `hM` using `[Nat.add_sub_cancel]`. Rewrite using `[add_mul]`. Use linear arithmetic over natural numbers and integers.

Rewrite `h6` using `[h4]`. Conclude with `Nat.le_of_mul_le_mul_left h6 (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exc_of_dvd {g d a l s : ℕ} (hg : 2 ≤ g) (ha : 0 < a) (had : a < d) (hl : l.Prime)
    (h : g ^ d - 1 ∣ (g ^ a - 1) * l ^ s) : Exc g d l := by
  refine ⟨hl, ?_⟩
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨e, he⟩ : ∃ e, e = Nat.gcd d a := ⟨_, rfl⟩
  have h2 : g ^ d - 1 ∣ (g ^ e - 1) * l ^ s := by
    rw [he, ← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_right]
    exact Nat.dvd_gcd (Dvd.intro _ rfl) h
  have hed : e ∣ d := he ▸ Nat.gcd_dvd_left d a
  have hea : e ≤ a := he ▸ Nat.gcd_le_right d ha
  have he0 : 0 < e := he ▸ Nat.gcd_pos_of_pos_right d ha
  have h2e : 2 * e ≤ d := by
    obtain ⟨c, rfl⟩ := hed
    rcases c with _ | _ | c
    · omega
    · omega
    · nlinarith
  obtain ⟨M, hM⟩ : g ^ e - 1 ∣ g ^ d - 1 := Nat.pow_sub_one_dvd_pow_sub_one g hed
  have hD : 1 < g ^ e := Nat.one_lt_pow he0.ne' (by omega)
  have hd1 : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
  rw [hM] at h2
  obtain ⟨t, -, rfl⟩ := (Nat.dvd_prime_pow hl).1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2)
  have ht : t ≤ padicValNat l (g ^ d - 1) :=
    (padicValNat_dvd_iff_le (by omega)).1 ⟨_, by rw [hM, mul_comm]⟩
  have h3 : g ^ (d - e) ≤ l ^ t := by
    have h4 : g ^ d = g ^ e * g ^ (d - e) := by rw [← pow_add]; congr 1; omega
    have h5 : 1 ≤ l ^ t := Nat.one_le_pow _ _ hl.pos
    have h6 : g ^ d ≤ g ^ e * l ^ t := by
      obtain ⟨A, hA⟩ : ∃ A, g ^ e = A + 1 := ⟨g ^ e - 1, by omega⟩
      rw [hA] at hM ⊢
      rw [Nat.add_sub_cancel] at hM
      rw [add_mul]
      omega
    rw [h4] at h6
    exact Nat.le_of_mul_le_mul_left h6 (by omega)
  calc g ^ d < g ^ ((d - e) * 4) := Nat.pow_lt_pow_right (by omega) (by omega)
    _ = (g ^ (d - e)) ^ 4 := pow_mul _ _ _
    _ ≤ (l ^ t) ^ 4 := Nat.pow_le_pow_left h3 _
    _ = l ^ (4 * t) := by rw [← pow_mul, mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right hl.pos (by omega)

/- English proof (translation)
Take `⟨M, hM⟩ : g - 1 ∣ g ^ d - 1` from `by simpa using Nat.pow_sub_one_dvd_pow_sub_one g (one_dvd d)`. Establish `h2` using `h`. Rewrite `h2` using `[hM]`. Take `⟨t, -, rfl⟩` from `(Nat.dvd_prime_pow hl).1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2)`. Establish `hbig : d < l ^ t`.

Take `⟨a, rfl⟩ : ∃ a, g = a + 1` from `⟨g - 1, by omega⟩`. Take `⟨n, rfl⟩ : ∃ n, d = n + 1` from `⟨d - 1, by omega⟩`. Establish `h3 : 1 + n * a ≤ (1 + a) ^ n`. Use `one_add_mul_le_pow (a := (a : ℤ)) (by omega) n` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Rewrite `hM` using `[Nat.add_sub_cancel, pow_succ, add_comm a 1]`. Establish `h4 : (1 + n * a) * (1 + a) ≤ (1 + a) ^ n * (1 + a)` using `Nat.mul_le_mul_right _ h3`. Establish `h5 : a * (n + 1) < a * l ^ t`. Establish `: 1 ≤ n * a * a` using `Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)`. Establish `h6 : (1 + n * a) * (1 + a) = 1 + a * (n + 1) + n * a * a` using `by ring`.

Use linear arithmetic over natural numbers and integers. Conclude with `lt_of_mul_lt_mul_left h5 (Nat.zero_le _)`. Use `⟨?_, fun hdv => ?_⟩` and prove the remaining obligations. Break down `t with _ | t` into its components or cases. Simplify using `at hbig`.

Use linear arithmetic over natural numbers and integers. Conclude with `⟨t, hM⟩`. Establish `hd1 : 1 ≤ g ^ d` using `Nat.one_le_pow _ _ (by omega)`. Establish `hZ : (g : ℤ) ^ d - 1 ^ d = ((g : ℤ) - 1) * (l : ℤ) ^ t` using `by zify [hd1, (by omega : 1 ≤ g)] at hM`. Rewrite using `[one_pow, hM]`.

Establish `hdZ : (l : ℤ) ∣ (g : ℤ) - 1` using `by zify [(by omega : 1 ≤ g)] at hdv`. Conclude with `hdv`. Establish `hlZ : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hl`. Establish `hng : ¬ (l : ℤ) ∣ (g : ℤ)` using `fun h' => hlZ.not_dvd_one (by simpa using dvd_sub h' hdZ)`. Establish `hlte : emultiplicity (l : ℤ) ((g : ℤ) ^ d - 1 ^ d) = emultiplicity (l : ℤ) ((g : ℤ) - 1) + emultiplicity (l : ℤ) (d : ℤ)`.

Break down `hl.eq_two_or_odd' with rfl | ho` into its components or cases. Conclude with `Int.two_pow_sub_pow' d (by omega) hng`. Rewrite using `[Int.emultiplicity_pow_sub_pow hl ho hdZ hng d, Int.natCast_emultiplicity]`. Rewrite `hlte` using `[hZ, emultiplicity_mul hlZ, emultiplicity_pow_self_of_prime hlZ]`. Establish `hfin : emultiplicity (l : ℤ) ((g : ℤ) - 1) ≠ ⊤` using `finiteMultiplicity_iff_emultiplicity_ne_top.1 (FiniteMultiplicity.of_prime_left hlZ (by omega))`.

Establish `h7` using `WithTop.add_left_cancel hfin hlte`. Establish `h8 : (l : ℤ) ^ t ∣ (d : ℤ)` using `pow_dvd_of_le_emultiplicity h7.le`. Establish `h9 : l ^ t ∣ d` using `by exact_mod_cast h8`. Use `Nat.le_of_dvd (by omega) h9` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_of_dvd {g d l s : ℕ} (hg : 2 ≤ g) (hg4 : g % 4 = 1) (hd : 2 ≤ d) (hl : l.Prime)
    (h : g ^ d - 1 ∣ (g - 1) * l ^ s) : (∃ t, g ^ d - 1 = (g - 1) * l ^ (t + 1)) ∧ ¬ l ∣ g - 1 := by
  obtain ⟨M, hM⟩ : g - 1 ∣ g ^ d - 1 := by simpa using Nat.pow_sub_one_dvd_pow_sub_one g (one_dvd d)
  have h2 := h
  rw [hM] at h2
  obtain ⟨t, -, rfl⟩ := (Nat.dvd_prime_pow hl).1 (Nat.dvd_of_mul_dvd_mul_left (by omega) h2)
  have hbig : d < l ^ t := by
    obtain ⟨a, rfl⟩ : ∃ a, g = a + 1 := ⟨g - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have h3 : 1 + n * a ≤ (1 + a) ^ n := by
      have := one_add_mul_le_pow (a := (a : ℤ)) (by omega) n
      exact_mod_cast this
    rw [Nat.add_sub_cancel, pow_succ, add_comm a 1] at hM
    have h4 : (1 + n * a) * (1 + a) ≤ (1 + a) ^ n * (1 + a) := Nat.mul_le_mul_right _ h3
    have h5 : a * (n + 1) < a * l ^ t := by
      have : 1 ≤ n * a * a := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
      have h6 : (1 + n * a) * (1 + a) = 1 + a * (n + 1) + n * a * a := by ring
      omega
    exact lt_of_mul_lt_mul_left h5 (Nat.zero_le _)
  refine ⟨?_, fun hdv => ?_⟩
  · rcases t with _ | t
    · simp at hbig; omega
    · exact ⟨t, hM⟩
  · have hd1 : 1 ≤ g ^ d := Nat.one_le_pow _ _ (by omega)
    have hZ : (g : ℤ) ^ d - 1 ^ d = ((g : ℤ) - 1) * (l : ℤ) ^ t := by
      zify [hd1, (by omega : 1 ≤ g)] at hM
      rw [one_pow, hM]
    have hdZ : (l : ℤ) ∣ (g : ℤ) - 1 := by
      zify [(by omega : 1 ≤ g)] at hdv
      exact hdv
    have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    have hng : ¬ (l : ℤ) ∣ (g : ℤ) := fun h' => hlZ.not_dvd_one (by simpa using dvd_sub h' hdZ)
    have hlte : emultiplicity (l : ℤ) ((g : ℤ) ^ d - 1 ^ d) =
        emultiplicity (l : ℤ) ((g : ℤ) - 1) + emultiplicity (l : ℤ) (d : ℤ) := by
      rcases hl.eq_two_or_odd' with rfl | ho
      · exact Int.two_pow_sub_pow' d (by omega) hng
      · rw [Int.emultiplicity_pow_sub_pow hl ho hdZ hng d, Int.natCast_emultiplicity]
    rw [hZ, emultiplicity_mul hlZ, emultiplicity_pow_self_of_prime hlZ] at hlte
    have hfin : emultiplicity (l : ℤ) ((g : ℤ) - 1) ≠ ⊤ :=
      finiteMultiplicity_iff_emultiplicity_ne_top.1 (FiniteMultiplicity.of_prime_left hlZ (by omega))
    have h7 := WithTop.add_left_cancel hfin hlte
    have h8 : (l : ℤ) ^ t ∣ (d : ℤ) := pow_dvd_of_le_emultiplicity h7.le
    have h9 : l ^ t ∣ d := by exact_mod_cast h8
    have := Nat.le_of_dvd (by omega) h9
    omega

/- English proof (translation)
Use `⟨(orderOf x).factorization l, ?_⟩` and prove the remaining obligations. Unfold `primeToPart`. Use `set n := orderOf x with hn`. Use `set A := l ^ n.factorization l with hA`. Establish `hn0 : n ≠ 0` using `hx.orderOf_pos.ne'`.

Establish `hAm : A * (n / A) = n` using `Nat.ordProj_mul_ordCompl_eq_self n l`. Establish `hcop : Nat.Coprime A (n / A)` using `(Nat.coprime_ordCompl hl hn0).pow_left _`. Establish `h1 : A * ((A : ZMod (n / A))⁻¹).val ≡ 1 [MOD n / A]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one]`. Conclude with `ZMod.mul_val_inv hcop`.

Rewrite using `[← pow_mul, hx.pow_eq_pow_iff_modEq, ← hn]`. Establish `h2` using `h1.mul_left' A`. Rewrite `h2` using `[hAm, mul_one]`. Rewrite using `[mul_comm]` and apply the resulting hypothesis.
-/
theorem pow_primeToPart {M : Type*} [Monoid M] {l : ℕ} (hl : l.Prime) {x : M} (hx : IsOfFinOrder x) :
    ∃ a, primeToPart l x ^ l ^ a = x ^ l ^ a := by
  refine ⟨(orderOf x).factorization l, ?_⟩
  unfold primeToPart
  set n := orderOf x with hn
  set A := l ^ n.factorization l with hA
  have hn0 : n ≠ 0 := hx.orderOf_pos.ne'
  have hAm : A * (n / A) = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hcop : Nat.Coprime A (n / A) := (Nat.coprime_ordCompl hl hn0).pow_left _
  have h1 : A * ((A : ZMod (n / A))⁻¹).val ≡ 1 [MOD n / A] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one]
    exact ZMod.mul_val_inv hcop
  rw [← pow_mul, hx.pow_eq_pow_iff_modEq, ← hn]
  have h2 := h1.mul_left' A
  rw [hAm, mul_one] at h2
  rwa [mul_comm]

/- English proof (translation)
Take `⟨a, ha⟩` from `pow_primeToPart hl hx`. Take `⟨b, hb⟩` from `pow_primeToPart hl hy`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, pow_mul, ← ha, h, ← pow_mul, mul_comm, pow_mul, hb, ← pow_mul]`.
-/
theorem exists_pow_eq {M : Type*} [Monoid M] {l : ℕ} (hl : l.Prime) {x y : M} (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart l x = primeToPart l y) : ∃ s, x ^ l ^ s = y ^ l ^ s := by
  obtain ⟨a, ha⟩ := pow_primeToPart hl hx
  obtain ⟨b, hb⟩ := pow_primeToPart hl hy
  refine ⟨a + b, ?_⟩
  rw [pow_add, pow_mul, ← ha, h, ← pow_mul, mul_comm, pow_mul, hb, ← pow_mul]

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Take `⟨f, hf⟩` from `GlobalTheory.CuspGL.exists_algHom_pow_card_pow (F := ZMod g) i`. Apply `f.injective` to reduce the goal to its premises. Use `show f _ = f _`. Rewrite using `[hf, hf, Nat.card_zmod, h]`.
-/
theorem frob_inj (i : ℕ) {x y : Fbar g} (h : x ^ g ^ i = y ^ g ^ i) : x = y := by
  obtain ⟨f, hf⟩ := GlobalTheory.CuspGL.exists_algHom_pow_card_pow (F := ZMod g) i
  apply f.injective
  show f _ = f _
  rw [hf, hf, Nat.card_zmod, h]

/- English proof (translation)
Rewrite using `[← map_pow, ZMod.pow_card_pow]`.
-/
theorem frob_fix (i : ℕ) (c : ZMod g) :
    algebraMap (ZMod g) (Fbar g) c ^ g ^ i = algebraMap (ZMod g) (Fbar g) c := by
  rw [← map_pow, ZMod.pow_card_pow]

/- English proof (translation)
Simplify `(GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (F := ZMod g) x _).1 dvd_rfl` using `[Nat.card_zmod]`.
-/
theorem pow_deg (x : Fbar g) : x ^ g ^ (minpoly (ZMod g) x).natDegree = x := by
  simpa [Nat.card_zmod] using (GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (F := ZMod g) x _).1 dvd_rfl

/- English proof (translation)
Establish `h` using `pow_deg x`. Establish `h1 : 1 < g ^ (minpoly (ZMod g) x).natDegree` using `Nat.one_lt_pow (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne' (Fact.out : g.Prime).one_lt`. Use `isOfFinOrder_iff_pow_eq_one.2 ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ hx` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel h1.le, h, one_mul]`.
-/
theorem finOrder {x : Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have h := pow_deg x
  have h1 : 1 < g ^ (minpoly (ZMod g) x).natDegree :=
    Nat.one_lt_pow (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne' (Fact.out : g.Prime).one_lt
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨g ^ (minpoly (ZMod g) x).natDegree - 1, by omega, ?_⟩
  apply mul_right_cancel₀ hx
  rw [← pow_succ, Nat.sub_add_cancel h1.le, h, one_mul]

/- English proof (translation)
Unfold `rootsBar at h`. Rewrite `h` using `[GlobalTheory.CuspGL.roots_minpoly_eq_map_range (F := ZMod g) x, Nat.card_zmod]`. Take `⟨i, hi, rfl⟩` from `Multiset.mem_map.1 h`. Conclude with `⟨i, Multiset.mem_range.1 hi, rfl⟩`.
-/
theorem mem_roots_minpoly {x y : Fbar g} (h : y ∈ rootsBar (minpoly (ZMod g) x)) :
    ∃ i, i < (minpoly (ZMod g) x).natDegree ∧ y = x ^ g ^ i := by
  unfold rootsBar at h
  rw [GlobalTheory.CuspGL.roots_minpoly_eq_map_range (F := ZMod g) x, Nat.card_zmod] at h
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 h
  exact ⟨i, Multiset.mem_range.1 hi, rfl⟩

def Gen (d : ℕ) (T : Finset (ZMod g)ˣ) (x : Fbar g) : Prop :=
  x ≠ 0 ∧ (minpoly (ZMod g) x).natDegree = d ∧
    (∀ l s a : ℕ, l.Prime → 0 < a → a < d → (x ^ l ^ s) ^ g ^ a = x ^ l ^ s → Exc g d l) ∧
    ∀ l s : ℕ, l.Prime → ∀ t ∈ T, x ^ l ^ s ≠ algebraMap (ZMod g) (Fbar g) (t : ZMod g) ^ l ^ s

/- English proof (translation)
Establish `hp : g.Prime` using `Fact.out`. Establish `hg` using `hp.two_le`. Establish `hd1 : 1 < g ^ d` using `Nat.one_lt_pow (by omega) hp.one_lt`. Use `haveI : NeZero (g ^ d - 1) := ⟨by omega⟩`. Use `haveI : NeZero ((g ^ d - 1 : ℕ) : ZMod g) := ⟨by`.

Rewrite using `[Nat.cast_sub hd1.le]`. Simplify using `[show d ≠ 0 by omega]⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (Fbar g) (g ^ d - 1)`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero (by omega)`. Set `A` to `algebraMap (ZMod g) (Fbar g)`.

Establish `hA0 : ∀ c : (ZMod g)ˣ, A c ≠ 0` using `fun c => by simp [A]`. Establish `core : ∀ (c : (ZMod g)ˣ) (n a : ℕ), ((A c * ζ) ^ n) ^ g ^ a = (A c * ζ) ^ n → g ^ d - 1 ∣ (g ^ a - 1) * n`. Introduce `c n a h`. Rewrite `h` using `[← pow_mul, mul_comm n, pow_mul, mul_pow (A c), frob_fix, mul_pow, mul_pow]`. Establish `h1` using `mul_left_cancel₀ (pow_ne_zero _ (hA0 c)) h`.

Establish `h2 : 1 ≤ g ^ a` using `Nat.one_le_pow _ _ hp.pos`. Rewrite using `[← hζ.pow_eq_one_iff_dvd]`. Apply `mul_right_cancel₀ (pow_ne_zero n hζ0)` to reduce the goal to its premises. Rewrite using `[one_mul, pow_mul, ← mul_pow, ← pow_succ, Nat.sub_add_cancel h2, h1]`. Establish `bad : ∀ (c t : (ZMod g)ˣ) (l s : ℕ), l.Prime → (A c * ζ) ^ l ^ s = A t ^ l ^ s → (∃ t, g ^ d - 1 = (g - 1) * l ^ (t + 1)) ∧ ¬ l ∣ g - 1`.

Introduce `c t l s hl h`. Use `pow_of_dvd (s := s) hg hg4 hd hl ?_` and prove the remaining obligations. Use `core c (l ^ s) 1 (by rw [h, ← map_pow, frob_fix])` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : (ZMod g)ˣ, ∀ l s : ℕ, l.Prime → ∀ t ∈ T, (A c * ζ) ^ l ^ s ≠ A t ^ l ^ s := by`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `choose l s hl t ht h using hne`. Establish `hinj : Function.Injective t`. Introduce `c c' htt`.

Take `⟨⟨u, hu⟩, hn⟩` from `bad c _ _ _ (hl c) (h c)`. Take `⟨⟨u', hu'⟩, -⟩` from `bad c' _ _ _ (hl c') (h c')`. Establish `hll : l c = l c'`. Establish `h1 : l c ^ (u + 1) = l c' ^ (u' + 1)` using `Nat.eq_of_mul_eq_mul_left (by omega) (hu.symm.trans hu')`. Conclude with `(Nat.prime_dvd_prime_iff_eq (hl c) (hl c')).1 ((hl c).dvd_of_dvd_pow (h1 ▸ dvd_pow_self _ (by omega)))`.

Establish `h1` using `h c`. Establish `h2` using `h c'`. Rewrite `h2` using `[← hll, ← htt]`. Establish `h3 : (A c * ζ) ^ l c ^ (s c + s c') = (A c' * ζ) ^ l c ^ (s c + s c')`. Rewrite using `[pow_add, pow_mul, h1, pow_right_comm, ← h2, pow_right_comm, ← pow_mul]`.

Rewrite `h3` using `[mul_pow, mul_pow]`. Establish `h4` using `mul_right_cancel₀ (pow_ne_zero _ hζ0) h3`. Rewrite `h4` using `[← map_pow, ← map_pow]`. Establish `h5 : c ^ l c ^ (s c + s c') = c' ^ l c ^ (s c + s c')` using `Units.ext (by simpa using A.injective h4)`. Establish `hcop : Nat.Coprime (Nat.card (ZMod g)ˣ) (l c ^ (s c + s c'))`.

Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Conclude with `(((hl c).coprime_iff_not_dvd.2 hn).symm).pow_right _`. Conclude with `(powCoprime hcop).injective h5`. Use `Finset.card_le_card_of_injOn (s := Finset.univ) (t := T) t (fun c _ => ht c) hinj.injOn` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, ZMod.card_units]`.

Use linear arithmetic over natural numbers and integers. Use `⟨A c * ζ, mul_ne_zero (hA0 c) hζ0, ?_, fun l s a hl ha had h => exc_of_dvd hg ha had hl (core c _ a h), hc⟩` and prove the remaining obligations. Establish `h1 : (minpoly (ZMod g) (A c * ζ)).natDegree ∣ d`. Rewrite using `[GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (F := ZMod g), Nat.card_zmod, mul_pow, frob_fix]`. Use `congr 1`.

Rewrite using `[← Nat.sub_add_cancel hd1.le, pow_succ, hζ.pow_eq_one, one_mul]`. Assume the negation of the conclusion as `hne`. Establish `h2` using `lt_of_le_of_ne (Nat.le_of_dvd (by omega) h1) hne`. Establish `h3` using `minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := ZMod g) (A c * ζ))`. Establish `h4` using `core c 1 _ (by rw [pow_one]; exact pow_deg _)`.

Establish `h5 : 1 < g ^ (minpoly (ZMod g) (A c * ζ)).natDegree` using `Nat.one_lt_pow h3.ne' hp.one_lt`. Establish `h6` using `Nat.pow_lt_pow_right hp.one_lt h2`. Use `Nat.le_of_dvd (by omega) h4` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_gen (hg4 : g % 4 = 1) {d : ℕ} (hd : 2 ≤ d) (T : Finset (ZMod g)ˣ) (hT : T.card + 1 < g) :
    ∃ x : Fbar g, Gen d T x := by
  have hp : g.Prime := Fact.out
  have hg := hp.two_le
  have hd1 : 1 < g ^ d := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (g ^ d - 1) := ⟨by omega⟩
  haveI : NeZero ((g ^ d - 1 : ℕ) : ZMod g) := ⟨by
    rw [Nat.cast_sub hd1.le]
    simp [show d ≠ 0 by omega]⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Fbar g) (g ^ d - 1)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  let A := algebraMap (ZMod g) (Fbar g)
  have hA0 : ∀ c : (ZMod g)ˣ, A c ≠ 0 := fun c => by simp [A]
  have core : ∀ (c : (ZMod g)ˣ) (n a : ℕ), ((A c * ζ) ^ n) ^ g ^ a = (A c * ζ) ^ n → g ^ d - 1 ∣ (g ^ a - 1) * n := by
    intro c n a h
    rw [← pow_mul, mul_comm n, pow_mul, mul_pow (A c), frob_fix, mul_pow, mul_pow] at h
    have h1 := mul_left_cancel₀ (pow_ne_zero _ (hA0 c)) h
    have h2 : 1 ≤ g ^ a := Nat.one_le_pow _ _ hp.pos
    rw [← hζ.pow_eq_one_iff_dvd]
    apply mul_right_cancel₀ (pow_ne_zero n hζ0)
    rw [one_mul, pow_mul, ← mul_pow, ← pow_succ, Nat.sub_add_cancel h2, h1]
  have bad : ∀ (c t : (ZMod g)ˣ) (l s : ℕ), l.Prime → (A c * ζ) ^ l ^ s = A t ^ l ^ s →
      (∃ t, g ^ d - 1 = (g - 1) * l ^ (t + 1)) ∧ ¬ l ∣ g - 1 := by
    intro c t l s hl h
    refine pow_of_dvd (s := s) hg hg4 hd hl ?_
    have := core c (l ^ s) 1 (by rw [h, ← map_pow, frob_fix])
    rwa [pow_one] at this
  obtain ⟨c, hc⟩ : ∃ c : (ZMod g)ˣ, ∀ l s : ℕ, l.Prime → ∀ t ∈ T, (A c * ζ) ^ l ^ s ≠ A t ^ l ^ s := by
    by_contra hne
    push Not at hne
    choose l s hl t ht h using hne
    have hinj : Function.Injective t := by
      intro c c' htt
      obtain ⟨⟨u, hu⟩, hn⟩ := bad c _ _ _ (hl c) (h c)
      obtain ⟨⟨u', hu'⟩, -⟩ := bad c' _ _ _ (hl c') (h c')
      have hll : l c = l c' := by
        have h1 : l c ^ (u + 1) = l c' ^ (u' + 1) := Nat.eq_of_mul_eq_mul_left (by omega) (hu.symm.trans hu')
        exact (Nat.prime_dvd_prime_iff_eq (hl c) (hl c')).1
          ((hl c).dvd_of_dvd_pow (h1 ▸ dvd_pow_self _ (by omega)))
      have h1 := h c
      have h2 := h c'
      rw [← hll, ← htt] at h2
      have h3 : (A c * ζ) ^ l c ^ (s c + s c') = (A c' * ζ) ^ l c ^ (s c + s c') := by
        rw [pow_add, pow_mul, h1, pow_right_comm, ← h2, pow_right_comm, ← pow_mul]
      rw [mul_pow, mul_pow] at h3
      have h4 := mul_right_cancel₀ (pow_ne_zero _ hζ0) h3
      rw [← map_pow, ← map_pow] at h4
      have h5 : c ^ l c ^ (s c + s c') = c' ^ l c ^ (s c + s c') := Units.ext (by simpa using A.injective h4)
      have hcop : Nat.Coprime (Nat.card (ZMod g)ˣ) (l c ^ (s c + s c')) := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units]
        exact (((hl c).coprime_iff_not_dvd.2 hn).symm).pow_right _
      exact (powCoprime hcop).injective h5
    have := Finset.card_le_card_of_injOn (s := Finset.univ) (t := T) t (fun c _ => ht c) hinj.injOn
    rw [Finset.card_univ, ZMod.card_units] at this
    omega
  refine ⟨A c * ζ, mul_ne_zero (hA0 c) hζ0, ?_, fun l s a hl ha had h => exc_of_dvd hg ha had hl (core c _ a h), hc⟩
  have h1 : (minpoly (ZMod g) (A c * ζ)).natDegree ∣ d := by
    rw [GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (F := ZMod g), Nat.card_zmod, mul_pow, frob_fix]
    congr 1
    rw [← Nat.sub_add_cancel hd1.le, pow_succ, hζ.pow_eq_one, one_mul]
  by_contra hne
  have h2 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) h1) hne
  have h3 := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := ZMod g) (A c * ζ))
  have h4 := core c 1 _ (by rw [pow_one]; exact pow_deg _)
  have h5 : 1 < g ^ (minpoly (ZMod g) (A c * ζ)).natDegree := Nat.one_lt_pow h3.ne' hp.one_lt
  have h6 := Nat.pow_lt_pow_right hp.one_lt h2
  have := Nat.le_of_dvd (by omega) h4
  omega

/- English proof (translation)
Take `⟨i, -, rfl⟩` from `mem_roots_minpoly hy`. Conclude with `pow_ne_zero _ h.1`.
-/
theorem Gen.root_ne {d : ℕ} {T : Finset (ZMod g)ˣ} {x y : Fbar g} (h : Gen d T x)
    (hy : y ∈ rootsBar (minpoly (ZMod g) x)) : y ≠ 0 := by
  obtain ⟨i, -, rfl⟩ := mem_roots_minpoly hy
  exact pow_ne_zero _ h.1

/- English proof (translation)
Introduce `he`. Take `⟨s, hs⟩` from `exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (by simp)) he`. Take `⟨i, -, rfl⟩` from `mem_roots_minpoly hy`. Use `h.2.2.2 l s hl t ht (frob_inj i ?_)` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, hs, ← map_pow, frob_fix]`.
-/
theorem Gen.avoid {d : ℕ} {T : Finset (ZMod g)ˣ} {x y : Fbar g} (h : Gen d T x) {l : ℕ} (hl : l.Prime)
    (hy : y ∈ rootsBar (minpoly (ZMod g) x)) {t : (ZMod g)ˣ} (ht : t ∈ T) :
    primeToPart l y ≠ primeToPart l (algebraMap (ZMod g) (Fbar g) (t : ZMod g)) := by
  intro he
  obtain ⟨s, hs⟩ := exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (by simp)) he
  obtain ⟨i, -, rfl⟩ := mem_roots_minpoly hy
  refine h.2.2.2 l s hl t ht (frob_inj i ?_)
  rw [← pow_mul, mul_comm, pow_mul, hs, ← map_pow, frob_fix]

/- English proof (translation)
Take `⟨i, -, rfl⟩` from `mem_roots_minpoly hy`. Use `h.2.2.1 l s a hl ha had (frob_inj i ?_)` and prove the remaining obligations. Rewrite using `[pow_right_comm (x ^ l ^ s), pow_right_comm x (l ^ s), he]`.
-/
theorem Gen.exc {d : ℕ} {T : Finset (ZMod g)ˣ} {x y : Fbar g} (h : Gen d T x) {l s a : ℕ} (hl : l.Prime)
    (hy : y ∈ rootsBar (minpoly (ZMod g) x)) (ha : 0 < a) (had : a < d) (he : (y ^ l ^ s) ^ g ^ a = y ^ l ^ s) :
    Exc g d l := by
  obtain ⟨i, -, rfl⟩ := mem_roots_minpoly hy
  refine h.2.2.1 l s a hl ha had (frob_inj i ?_)
  rw [pow_right_comm (x ^ l ^ s), pow_right_comm x (l ^ s), he]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (h.root_ne hz)) he`. Use `clear he`. Take `⟨i, hi, hyi⟩` from `mem_roots_minpoly hy`. Take `⟨j, hj, hzj⟩` from `mem_roots_minpoly hz`. Rewrite `hi`, `hj` using `[h.2.1]`.

Use `wlog hij : i ≤ j generalizing y z i j`. Conclude with `(this hz hy hs.symm j hj hzj i hi hyi (by omega)).symm`. Break down `hij.eq_or_lt with rfl | hij` into its components or cases. Rewrite using `[hyi, hzj]`. Use `absurd (h.exc (s := s) (a := j - i) hl hy (by omega) (by omega) ?_) hn` and prove the remaining obligations.

Rewrite using `[pow_right_comm, hs, hyi, hzj, ← pow_mul x, ← pow_add, Nat.add_sub_cancel' hij.le]`.
-/
theorem Gen.apart {d : ℕ} {T : Finset (ZMod g)ˣ} {x y z : Fbar g} (h : Gen d T x) {l : ℕ} (hl : l.Prime)
    (hn : ¬ Exc g d l) (hy : y ∈ rootsBar (minpoly (ZMod g) x)) (hz : z ∈ rootsBar (minpoly (ZMod g) x))
    (he : primeToPart l y = primeToPart l z) : y = z := by
  obtain ⟨s, hs⟩ := exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (h.root_ne hz)) he
  clear he
  obtain ⟨i, hi, hyi⟩ := mem_roots_minpoly hy
  obtain ⟨j, hj, hzj⟩ := mem_roots_minpoly hz
  rw [h.2.1] at hi hj
  wlog hij : i ≤ j generalizing y z i j
  · exact (this hz hy hs.symm j hj hzj i hi hyi (by omega)).symm
  rcases hij.eq_or_lt with rfl | hij
  · rw [hyi, hzj]
  · refine absurd (h.exc (s := s) (a := j - i) hl hy (by omega) (by omega) ?_) hn
    rw [pow_right_comm, hs, hyi, hzj, ← pow_mul x, ← pow_add, Nat.add_sub_cancel' hij.le]

/- English proof (translation)
Introduce `he`. Take `⟨s, hs⟩` from `exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (h'.root_ne hz)) he`. Use `hn (h.exc (s := s) hl hy he0 hed ?_)` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `mem_roots_minpoly hz`. Use `pow_deg x'` as an intermediate fact.

Rewrite `this` using `[h'.2.1]`. Rewrite using `[hs, pow_right_comm, pow_right_comm x' (g ^ j), this]`.
-/
theorem Gen.cross {d e : ℕ} {T : Finset (ZMod g)ˣ} {x x' y z : Fbar g} (h : Gen d T x) (h' : Gen e T x') (he0 : 0 < e)
    (hed : e < d) {l : ℕ} (hl : l.Prime) (hn : ¬ Exc g d l) (hy : y ∈ rootsBar (minpoly (ZMod g) x))
    (hz : z ∈ rootsBar (minpoly (ZMod g) x')) : primeToPart l y ≠ primeToPart l z := by
  intro he
  obtain ⟨s, hs⟩ := exists_pow_eq hl (finOrder (h.root_ne hy)) (finOrder (h'.root_ne hz)) he
  refine hn (h.exc (s := s) hl hy he0 hed ?_)
  obtain ⟨j, -, rfl⟩ := mem_roots_minpoly hz
  have := pow_deg x'
  rw [h'.2.1] at this
  rw [hs, pow_right_comm, pow_right_comm x' (g ^ j), this]

/- English proof (translation)
Unfold `rootsBar at *`. Rewrite `h` using `[Polynomial.map_mul, roots_mul (mul_ne_zero (hP.map _).ne_zero (hQ.map _).ne_zero), Multiset.mem_add]`. Then use the resulting hypothesis.
-/
theorem mem_rootsBar_mul {P Q : (ZMod g)[X]} (hP : P.Monic) (hQ : Q.Monic) {y : Fbar g} (h : y ∈ rootsBar (P * Q)) :
    y ∈ rootsBar P ∨ y ∈ rootsBar Q := by
  unfold rootsBar at *
  rwa [Polynomial.map_mul, roots_mul (mul_ne_zero (hP.map _).ne_zero (hQ.map _).ne_zero), Multiset.mem_add] at h

/- English proof (translation)
Take `⟨p, hp, hp1, hp2⟩` from `exists_prime_window N hN`. Take `⟨v₀, v₁, hv⟩` from `exists_pair_ne PP`. Use `choose a ha using fun v => exists_gen hg4 (d := N) (by omega) (T v) (hT v)`. Use `choose b hb using fun v => exists_gen hg4 (d := p) (by omega) (T v) (hT v)`. Use `choose c hc using fun v => exists_gen hg4 (d := N - p) (by omega) (T v) (hT v)`.

Establish `hi : ∀ x : Fbar g, IsIntegral (ZMod g) x` using `fun x => Algebra.IsIntegral.isIntegral x`. Establish `hm : ∀ x : Fbar g, (minpoly (ZMod g) x).Monic` using `fun x => minpoly.monic (hi x)`. Establish `hirr : ∀ x : Fbar g, Irreducible (minpoly (ZMod g) x)` using `fun x => minpoly.irreducible (hi x)`. Use `⟨fun v => if v = v₀ then minpoly (ZMod g) (a v) else minpoly (ZMod g) (b v) * minpoly (ZMod g) (c v), fun J χ hχ => ⟨fun v => ?_, fun v => ?_, fun l hl hB v => ?_, fun l hl _ v j => ?_, fun k hk1 hk2 => ⟨v₀, ?_⟩, v₁, minpoly (ZMod g) (b v₁), hirr _, ?_, ?_⟩⟩` and prove the remaining obligations. Use `beta_reduce split_ifs`.

Conclude with `⟨hm _, (ha v).2.1, minpoly.coeff_zero_ne_zero (hi _) (ha v).1⟩`. Use `⟨(hm _).mul (hm _), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(hm _).natDegree_mul (hm _), (hb v).2.1, (hc v).2.1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mul_coeff_zero]`.

Conclude with `mul_ne_zero (minpoly.coeff_zero_ne_zero (hi _) (hb v).1) (minpoly.coeff_zero_ne_zero (hi _) (hc v).1)`. Use `beta_reduce split_ifs`. Conclude with `(hirr _).squarefree`. Use `squarefree_mul_iff.2 ⟨?_, (hirr _).squarefree, (hirr _).squarefree⟩` and prove the remaining obligations. Use `(hirr _).isRelPrime_iff_not_dvd.2 fun h => ?_` and prove the remaining obligations.

Use `natDegree_le_of_dvd h (hm _).ne_zero` as an intermediate fact. Rewrite `this` using `[(hb v).2.1, (hc v).2.1]`. Use linear arithmetic over natural numbers and integers. Establish `hE : ∀ d, 1 ≤ d → d ≤ N → ¬ Exc g d l` using `fun d h1 h2 h => hB (Or.inr ⟨d, h1, h2, h⟩) beta_reduce split_ifs`. Conclude with `fun x hx y hy h => (ha v).apart hl (hE N (by omega) le_rfl) hx hy h`.

Introduce `x hx y hy h`. Apply the tactic sequence `rcases mem_rootsBar_mul (hm _) (hm _) hx with hx | hx <;> rcases mem_rootsBar_mul (hm _) (hm _) hy with hy | hy`. Conclude with `(hb v).apart hl (hE p (by omega) (by omega)) hx hy h`. Conclude with `absurd h ((hb v).cross (hc v) (by omega) (by omega) hl (hE p (by omega) (by omega)) hx hy)`. Conclude with `absurd h.symm ((hb v).cross (hc v) (by omega) (by omega) hl (hE p (by omega) (by omega)) hy hx)`.

Conclude with `(hc v).apart hl (hE (N - p) (by omega) (by omega)) hx hy h`. Use `beta_reduce split_ifs`. Conclude with `fun x hx => (ha v).avoid hl hx (hχ v j)`. Introduce `x hx`. Break down `mem_rootsBar_mul (hm _) (hm _) hx with hx | hx` into its components or cases.

Conclude with `(hb v).avoid hl hx (hχ v j)`. Conclude with `(hc v).avoid hl hx (hχ v j)`. Simplify using `only [if_true]`. Introduce and unpack `⟨q, ⟨r, hr⟩, hq⟩`. Break down `(hirr (a v₀)).isUnit_or_isUnit hr with h | h` into its components or cases.

Use `natDegree_eq_zero_of_isUnit h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h0` using `(hm (a v₀)).ne_zero`. Establish `h1` using `(ha v₀).2.1`. Rewrite `h0`, `h1` using `[hr]`.

Rewrite `h1` using `[natDegree_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), natDegree_eq_zero_of_isUnit h]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [if_neg hv.symm]`. Conclude with `dvd_mul_right _ _`. Rewrite using `[(hb v₁).2.1]`.

Conclude with `⟨hp, hp1, hp2⟩`.
-/
theorem exists_isGood (hg4 : g % 4 = 1) {N : ℕ} (hN : 8 ≤ N) {PP : Type} [Nontrivial PP] (T : PP → Finset (ZMod g)ˣ)
    (hT : ∀ v, (T v).card + 1 < g) :
    ∃ f : PP → (ZMod g)[X], ∀ (J : Type) (χ : PP → J → (ZMod g)ˣ), (∀ v j, χ v j ∈ T v) → IsGood N g f χ := by
  classical
  obtain ⟨p, hp, hp1, hp2⟩ := exists_prime_window N hN
  obtain ⟨v₀, v₁, hv⟩ := exists_pair_ne PP
  choose a ha using fun v => exists_gen hg4 (d := N) (by omega) (T v) (hT v)
  choose b hb using fun v => exists_gen hg4 (d := p) (by omega) (T v) (hT v)
  choose c hc using fun v => exists_gen hg4 (d := N - p) (by omega) (T v) (hT v)
  have hi : ∀ x : Fbar g, IsIntegral (ZMod g) x := fun x => Algebra.IsIntegral.isIntegral x
  have hm : ∀ x : Fbar g, (minpoly (ZMod g) x).Monic := fun x => minpoly.monic (hi x)
  have hirr : ∀ x : Fbar g, Irreducible (minpoly (ZMod g) x) := fun x => minpoly.irreducible (hi x)
  refine ⟨fun v => if v = v₀ then minpoly (ZMod g) (a v) else minpoly (ZMod g) (b v) * minpoly (ZMod g) (c v),
    fun J χ hχ => ⟨fun v => ?_, fun v => ?_, fun l hl hB v => ?_, fun l hl _ v j => ?_, fun k hk1 hk2 => ⟨v₀, ?_⟩,
      v₁, minpoly (ZMod g) (b v₁), hirr _, ?_, ?_⟩⟩
  · beta_reduce
    split_ifs
    · exact ⟨hm _, (ha v).2.1, minpoly.coeff_zero_ne_zero (hi _) (ha v).1⟩
    · refine ⟨(hm _).mul (hm _), ?_, ?_⟩
      · rw [(hm _).natDegree_mul (hm _), (hb v).2.1, (hc v).2.1]; omega
      · rw [mul_coeff_zero]
        exact mul_ne_zero (minpoly.coeff_zero_ne_zero (hi _) (hb v).1) (minpoly.coeff_zero_ne_zero (hi _) (hc v).1)
  · beta_reduce
    split_ifs
    · exact (hirr _).squarefree
    · refine squarefree_mul_iff.2 ⟨?_, (hirr _).squarefree, (hirr _).squarefree⟩
      refine (hirr _).isRelPrime_iff_not_dvd.2 fun h => ?_
      have := natDegree_le_of_dvd h (hm _).ne_zero
      rw [(hb v).2.1, (hc v).2.1] at this
      omega
  · have hE : ∀ d, 1 ≤ d → d ≤ N → ¬ Exc g d l := fun d h1 h2 h => hB (Or.inr ⟨d, h1, h2, h⟩)
    beta_reduce
    split_ifs
    · exact fun x hx y hy h => (ha v).apart hl (hE N (by omega) le_rfl) hx hy h
    · intro x hx y hy h
      rcases mem_rootsBar_mul (hm _) (hm _) hx with hx | hx <;> rcases mem_rootsBar_mul (hm _) (hm _) hy with hy | hy
      · exact (hb v).apart hl (hE p (by omega) (by omega)) hx hy h
      · exact absurd h ((hb v).cross (hc v) (by omega) (by omega) hl (hE p (by omega) (by omega)) hx hy)
      · exact absurd h.symm ((hb v).cross (hc v) (by omega) (by omega) hl (hE p (by omega) (by omega)) hy hx)
      · exact (hc v).apart hl (hE (N - p) (by omega) (by omega)) hx hy h
  · beta_reduce
    split_ifs
    · exact fun x hx => (ha v).avoid hl hx (hχ v j)
    · intro x hx
      rcases mem_rootsBar_mul (hm _) (hm _) hx with hx | hx
      · exact (hb v).avoid hl hx (hχ v j)
      · exact (hc v).avoid hl hx (hχ v j)
  · simp only [if_true]
    rintro ⟨q, ⟨r, hr⟩, hq⟩
    rcases (hirr (a v₀)).isUnit_or_isUnit hr with h | h
    · have := natDegree_eq_zero_of_isUnit h
      omega
    · have h0 := (hm (a v₀)).ne_zero
      have h1 := (ha v₀).2.1
      rw [hr] at h0 h1
      rw [natDegree_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), natDegree_eq_zero_of_isUnit h] at h1
      omega
  · simp only [if_neg hv.symm]
    exact dvd_mul_right _ _
  · rw [(hb v₁).2.1]
    exact ⟨hp, hp1, hp2⟩

end GlobalTheory.MemN.GoodEx

namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem

/- English proof (translation)
Establish `h1` using `B.R.m_le_f`. Establish `h2` using `B.R.f_le_k`. Establish `h3` using `B.R.two_le_m`. Establish `hn : 4 ≤ B.R.ord` using `B.host.four_le_n'`. Establish `hr : 8 ≤ B.R.r` using `by unfold Ranks.r; omega`.

Use `haveI : Nontrivial (Fin B.R.f) := Fin.nontrivial_iff_two_le.2 (by unfold Ranks.f Ranks.n; omega)`. Establish `key : ∀ k, haveI : Fact (B.host.g k).Prime` using `⟨B.host.g_prime k⟩ ∃ f : Fin B.R.f → Polynomial (ZMod (B.host.g k)), Formalism.CyclotomicNorms.IsGood B.R.r (B.host.g k) f (χ k) ∧ Formalism.CyclotomicNorms.IsGood B.R.r (B.host.g k) f (fun v j => (χ k v j)⁻¹) := by`. Introduce `k`. Use `haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩`. Establish `hbig : 2 * B.R.m + 1 < B.host.g k`.

Establish `hq` using `B.host.qd_big`. Establish `hc` using `B.g_cond k`. Establish `hg` using `(B.host.g_prime k).two_le`. Establish `h4 : B.host.QS * B.host.q * B.host.d < B.host.g k`. Assume the negation of the conclusion as `hlt`.

Break down `(not_lt.1 hlt).eq_or_lt with h | h` into its components or cases. Rewrite `hc` using `[← h, Nat.mod_self]`. Use linear arithmetic over natural numbers and integers. Rewrite `hc` using `[Nat.mod_eq_of_lt h]`. Use linear arithmetic over natural numbers and integers.

Establish `hQ` using `B.host.QS_pos`. Establish `h5 : 1 * B.host.q * 1 ≤ B.host.QS * B.host.q * B.host.d` using `Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)`. Establish `h6 : 4 * B.R.t * 1 ≤ 4 * B.R.t * B.R.r` using `Nat.mul_le_mul_left _ (by omega)`. Establish `h7` using `B.R.three_m_lt_t`. Use linear arithmetic over natural numbers and integers.

Take `⟨f, hf⟩` from `GoodEx.exists_isGood (B.level_mod_four _ (B.host.g_level k)) hr (fun v : Fin B.R.f => Finset.univ.image (χ k v) ∪ Finset.univ.image (fun j => (χ k v j)⁻¹)) (fun v => by`. Establish `a1` using `Finset.card_union_le (Finset.univ.image (χ k v)) (Finset.univ.image (fun j => (χ k v j)⁻¹))`. Establish `a2` using `Finset.card_image_le (s := Finset.univ) (f := χ k v)`. Establish `a3` using `Finset.card_image_le (s := Finset.univ) (f := fun j => (χ k v j)⁻¹)`. Rewrite `a2`, `a3` using `[Finset.card_univ, Fintype.card_fin]`.

Use the proof step `omega)`. Conclude with `⟨f, hf _ _ fun v j => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hf _ _ fun v j => Finset.mem_union_right _ (Finset.mem_image_of_mem (fun j => (χ k v j)⁻¹) (Finset.mem_univ j))⟩`. Use `choose f hf using key`. Conclude with `⟨f, hf⟩`.
-/
theorem goodChi (B : Pre) (χ : Chi B) : GoodChi B χ := by
  classical
  have h1 := B.R.m_le_f
  have h2 := B.R.f_le_k
  have h3 := B.R.two_le_m
  have hn : 4 ≤ B.R.ord := B.host.four_le_n'
  have hr : 8 ≤ B.R.r := by unfold Ranks.r; omega
  haveI : Nontrivial (Fin B.R.f) := Fin.nontrivial_iff_two_le.2 (by unfold Ranks.f Ranks.n; omega)
  have key : ∀ k, haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
      ∃ f : Fin B.R.f → Polynomial (ZMod (B.host.g k)), Formalism.CyclotomicNorms.IsGood B.R.r (B.host.g k) f (χ k) ∧
        Formalism.CyclotomicNorms.IsGood B.R.r (B.host.g k) f (fun v j => (χ k v j)⁻¹) := by
    intro k
    haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
    have hbig : 2 * B.R.m + 1 < B.host.g k := by
      have hq := B.host.qd_big
      have hc := B.g_cond k
      have hg := (B.host.g_prime k).two_le
      have h4 : B.host.QS * B.host.q * B.host.d < B.host.g k := by
        by_contra hlt
        rcases (not_lt.1 hlt).eq_or_lt with h | h
        · rw [← h, Nat.mod_self] at hc
          omega
        · rw [Nat.mod_eq_of_lt h] at hc
          omega
      have hQ := B.host.QS_pos
      have h5 : 1 * B.host.q * 1 ≤ B.host.QS * B.host.q * B.host.d :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) (by omega)
      have h6 : 4 * B.R.t * 1 ≤ 4 * B.R.t * B.R.r := Nat.mul_le_mul_left _ (by omega)
      have h7 := B.R.three_m_lt_t
      omega
    obtain ⟨f, hf⟩ := GoodEx.exists_isGood (B.level_mod_four _ (B.host.g_level k)) hr
      (fun v : Fin B.R.f => Finset.univ.image (χ k v) ∪ Finset.univ.image (fun j => (χ k v j)⁻¹)) (fun v => by
        have a1 := Finset.card_union_le (Finset.univ.image (χ k v)) (Finset.univ.image (fun j => (χ k v j)⁻¹))
        have a2 := Finset.card_image_le (s := Finset.univ) (f := χ k v)
        have a3 := Finset.card_image_le (s := Finset.univ) (f := fun j => (χ k v j)⁻¹)
        rw [Finset.card_univ, Fintype.card_fin] at a2 a3
        omega)
    exact ⟨f, hf _ _ fun v j => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)),
      hf _ _ fun v j => Finset.mem_union_right _ (Finset.mem_image_of_mem (fun j => (χ k v j)⁻¹) (Finset.mem_univ j))⟩
  choose f hf using key
  exact ⟨f, hf⟩

end GlobalTheory.MemN
