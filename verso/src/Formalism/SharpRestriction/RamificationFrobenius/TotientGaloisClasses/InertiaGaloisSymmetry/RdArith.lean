import Mathlib

open ArithmeticFunction Finset

noncomputable section

namespace Formalism.HC.Der.Rd

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih`. Rewrite using `[Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ hl, pow_succ]`. Establish `h1 : 1 ≤ l` using `hl.one_lt.le`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_totient_pow {l : ℕ} (hl : l.Prime) (s : ℕ) : ∑ k ∈ range (s + 1), (l ^ k).totient = l ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ hl, pow_succ]
    have h1 : 1 ≤ l := hl.one_lt.le
    calc l ^ s + l ^ s * (l - 1) = l ^ s * (1 + (l - 1)) := by ring
      _ = l ^ s * l := by congr 1; omega

/- English proof (translation)
Use `first`. Consider the case `exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'`. Consider the case `exact (Nat.totient_pos (Nat.pos_of_ne_zero hn)).ne'`. Consider the case `simpa using hn`.
-/
private theorem totient_ne_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.totient ≠ 0 := by
  first
  | exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  | exact (Nat.totient_pos (Nat.pos_of_ne_zero hn)).ne'
  | simpa using hn

/- English proof (translation)
Rewrite `hn`, the goal using `[isPrimePow_nat_iff]`. Take `⟨q, e, hq, he, rfl⟩` from `hn`. Take `⟨i, hi, rfl⟩` from `(Nat.dvd_prime_pow hq).1 hk`. Conclude with `⟨q, i, hq, Nat.pos_of_ne_zero (by rintro rfl; exact hk1 (pow_zero q)), rfl⟩`.
-/
private theorem isPrimePow_of_dvd_isPrimePow_of_ne_one {n k : ℕ} (hn : IsPrimePow n) (hk : k ∣ n) (hk1 : k ≠ 1) :
    IsPrimePow k := by
  rw [isPrimePow_nat_iff] at hn ⊢
  obtain ⟨q, e, hq, he, rfl⟩ := hn
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hq).1 hk
  exact ⟨q, i, hq, Nat.pos_of_ne_zero (by rintro rfl; exact hk1 (pow_zero q)), rfl⟩

/- English proof (translation)
Use `first`. Consider the case `exact Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'`. Consider the case `exact ⟨n.factorization p, n / p ^ n.factorization p, Nat.not_dvd_ordCompl hp hn, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩`.
-/
private theorem exists_eq_prime_pow_mul_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    ∃ v M : ℕ, ¬ p ∣ M ∧ n = p ^ v * M := by
  first
  | exact Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  | exact ⟨n.factorization p, n / p ^ n.factorization p, Nat.not_dvd_ordCompl hp hn,
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩

/- English proof (translation)
Use `first`. Consider the case `exact Nat.pow_dvd_pow_iff_le_right hp.one_lt`. Consider the case `exact pow_dvd_pow_iff_le hp.ne_zero hp.not_isUnit`. Consider the case `exact ⟨fun h => (Nat.pow_le_pow_iff_right hp.one_lt).mp (Nat.le_of_dvd (pow_pos hp.pos _) h), fun h => pow_dvd_pow p h⟩`.
-/
private theorem prime_pow_dvd_prime_pow_iff_le {p a b : ℕ} (hp : p.Prime) : p ^ a ∣ p ^ b ↔ a ≤ b := by
  first
  | exact Nat.pow_dvd_pow_iff_le_right hp.one_lt
  | exact pow_dvd_pow_iff_le hp.ne_zero hp.not_isUnit
  | exact ⟨fun h => (Nat.pow_le_pow_iff_right hp.one_lt).mp (Nat.le_of_dvd (pow_pos hp.pos _) h),
      fun h => pow_dvd_pow p h⟩

/- English proof (translation)
Distinguish the cases in `hpp : IsPrimePow m`. Use `swap`. Rewrite using `[vonMangoldt_eq_zero_iff.mpr hpp, zero_div, mul_zero]`. Use `Finset.sum_eq_zero fun m' hm' => ?_` and prove the remaining obligations. Rewrite `hm'` using `[Finset.mem_filter]`.

Establish `h0 : vonMangoldt m' = 0` using `vonMangoldt_eq_zero_iff.mpr fun h => hpp (isPrimePow_of_dvd_isPrimePow_of_ne_one h hm'.2 hm1)`. Rewrite using `[h0, zero_mul]`. Take `⟨p, j, hp, hj, rfl⟩` from `(isPrimePow_nat_iff _).mp hpp`. Establish `hex : ∃ v M : ℕ, ¬ p ∣ M ∧ N = p ^ v * M` using `exists_eq_prime_pow_mul_not_dvd hN hp`. Take `⟨v, M, hpM, rfl⟩` from `hex`.

Establish `hcop : Nat.Coprime p M` using `(Nat.Prime.coprime_iff_not_dvd hp).mpr hpM`. Establish `hdvd : ∀ k, p ^ k ∣ p ^ v * M ↔ k ≤ v` using `fun k => ⟨fun h => (prime_pow_dvd_prime_pow_iff_le hp).mp ((Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right h), fun h => (pow_dvd_pow p h).mul_right M⟩`. Establish `hjv : j ≤ v` using `(hdvd j).mp hm`. Establish `hsub : (range (v - j + 1)).image (fun i => p ^ (j + i)) ⊆ (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m')`. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_image]`. Take `⟨i, hi, rfl⟩` from `hx`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[Finset.mem_filter, Nat.mem_divisors]`. Conclude with `⟨⟨(hdvd _).mpr (by omega), hN⟩, pow_dvd_pow p (by omega)⟩`.

Establish `hzero : ∀ x ∈ (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m'), x ∉ (range (v - j + 1)).image (fun i => p ^ (j + i)) → vonMangoldt x * (((p ^ v * M) / x).totient : ℝ) = 0`. Introduce `x hx hxT`. Rewrite `hx` using `[Finset.mem_filter, Nat.mem_divisors]`. Assume the negation of the conclusion as `hne`. Establish `hx' : vonMangoldt x ≠ 0` using `fun h => hne (by rw [h, zero_mul])`.

Rewrite `hx'` using `[Ne, vonMangoldt_eq_zero_iff, not_not, isPrimePow_nat_iff]`. Take `⟨q, k, hq, hk, rfl⟩` from `hx'`. Establish `hpq : p = q` using `(Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow ((dvd_pow_self p hj.ne').trans hx.2))`. Substitute `hpq` using the available equality. Establish `hjk : j ≤ k` using `(prime_pow_dvd_prime_pow_iff_le hp).mp hx.2`.

Establish `hkv : k ≤ v` using `(hdvd k).mp hx.1.1`. Apply `hxT` to reduce the goal to its premises. Rewrite using `[Finset.mem_image]`. Conclude with `⟨k - j, Finset.mem_range.mpr (by omega), by congr 1; omega⟩`. Rewrite using `[← Finset.sum_subset hsub hzero]`.

Rewrite using `[Finset.sum_image (by`. Introduce `a _ b _ h`. Establish `h2 : j + a = j + b` using `Nat.pow_right_injective hp.two_le h`. Use the proof step `omega)]`. Establish `hterm : ∀ i ∈ range (v - j + 1), vonMangoldt (p ^ (j + i)) * (((p ^ v * M) / p ^ (j + i)).totient : ℝ) = Real.log p * (((p ^ (v - j - i)).totient * M.totient : ℕ) : ℝ)`.

Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]`. Establish `h1 : p ^ v * M = p ^ (j + i) * (p ^ (v - j - i) * M)`. Rewrite using `[← mul_assoc, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos _), Nat.totient_mul (Nat.Coprime.pow_left _ hcop)]`. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum]`. Establish `hsum : ∑ i ∈ range (v - j + 1), (p ^ (v - j - i)).totient * M.totient = p ^ (v - j) * M.totient`.

Rewrite using `[← Finset.sum_mul, ← sum_totient_pow hp (v - j)]`. Use `congr 1`. Rewrite using `[← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Nat.cast_sum, hsum]`. Establish `hphi : (p ^ v).totient = p ^ (v - j) * (p ^ j).totient`. Rewrite using `[Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp hj, ← mul_assoc, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `hpj : ((p ^ j).totient : ℝ) ≠ 0`. Conclude with `totient_ne_zero_of_ne_zero (pow_ne_zero j hp.ne_zero)` after adjusting the coercions. Rewrite using `[vonMangoldt_apply_pow hj.ne', vonMangoldt_apply_prime hp, Nat.totient_mul (Nat.Coprime.pow_left v hcop), hphi]`.

Establish `e : ((p ^ j).totient : ℝ) * (Real.log p / ((p ^ j).totient : ℝ)) = Real.log p` using `by first`. Consider the case `rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpj, mul_one]`. Consider the case `field_simp`. Use `push_cast`. Take the linear combination `(-((p : ℝ) ^ (v - j) * (M.totient : ℝ))) * e`.
-/
theorem weight_sum {N m : ℕ} (hN : N ≠ 0) (hm : m ∣ N) (hm1 : m ≠ 1) :
    ∑ m' ∈ N.divisors.filter (fun m' => m ∣ m'), vonMangoldt m' * ((N / m').totient : ℝ) =
      (N.totient : ℝ) * (vonMangoldt m / (m.totient : ℝ)) := by
  by_cases hpp : IsPrimePow m
  swap
  · rw [vonMangoldt_eq_zero_iff.mpr hpp, zero_div, mul_zero]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    rw [Finset.mem_filter] at hm'
    have h0 : vonMangoldt m' = 0 :=
      vonMangoldt_eq_zero_iff.mpr fun h => hpp (isPrimePow_of_dvd_isPrimePow_of_ne_one h hm'.2 hm1)
    rw [h0, zero_mul]
  obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hex : ∃ v M : ℕ, ¬ p ∣ M ∧ N = p ^ v * M := exists_eq_prime_pow_mul_not_dvd hN hp
  obtain ⟨v, M, hpM, rfl⟩ := hex
  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hdvd : ∀ k, p ^ k ∣ p ^ v * M ↔ k ≤ v := fun k =>
    ⟨fun h => (prime_pow_dvd_prime_pow_iff_le hp).mp ((Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right h),
      fun h => (pow_dvd_pow p h).mul_right M⟩
  have hjv : j ≤ v := (hdvd j).mp hm
  have hsub : (range (v - j + 1)).image (fun i => p ^ (j + i)) ⊆
      (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m') := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨(hdvd _).mpr (by omega), hN⟩, pow_dvd_pow p (by omega)⟩
  have hzero : ∀ x ∈ (p ^ v * M).divisors.filter (fun m' => p ^ j ∣ m'),
      x ∉ (range (v - j + 1)).image (fun i => p ^ (j + i)) →
        vonMangoldt x * (((p ^ v * M) / x).totient : ℝ) = 0 := by
    intro x hx hxT
    rw [Finset.mem_filter, Nat.mem_divisors] at hx
    by_contra hne
    have hx' : vonMangoldt x ≠ 0 := fun h => hne (by rw [h, zero_mul])
    rw [Ne, vonMangoldt_eq_zero_iff, not_not, isPrimePow_nat_iff] at hx'
    obtain ⟨q, k, hq, hk, rfl⟩ := hx'
    have hpq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow ((dvd_pow_self p hj.ne').trans hx.2))
    subst hpq
    have hjk : j ≤ k := (prime_pow_dvd_prime_pow_iff_le hp).mp hx.2
    have hkv : k ≤ v := (hdvd k).mp hx.1.1
    apply hxT
    rw [Finset.mem_image]
    exact ⟨k - j, Finset.mem_range.mpr (by omega), by congr 1; omega⟩
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (by
    intro a _ b _ h
    have h2 : j + a = j + b := Nat.pow_right_injective hp.two_le h
    omega)]
  have hterm : ∀ i ∈ range (v - j + 1), vonMangoldt (p ^ (j + i)) * (((p ^ v * M) / p ^ (j + i)).totient : ℝ) =
      Real.log p * (((p ^ (v - j - i)).totient * M.totient : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have h1 : p ^ v * M = p ^ (j + i) * (p ^ (v - j - i) * M) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    rw [h1, Nat.mul_div_cancel_left _ (pow_pos hp.pos _), Nat.totient_mul (Nat.Coprime.pow_left _ hcop)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum : ∑ i ∈ range (v - j + 1), (p ^ (v - j - i)).totient * M.totient = p ^ (v - j) * M.totient := by
    rw [← Finset.sum_mul, ← sum_totient_pow hp (v - j)]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  rw [← Nat.cast_sum, hsum]
  have hphi : (p ^ v).totient = p ^ (v - j) * (p ^ j).totient := by
    rw [Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp hj, ← mul_assoc, ← pow_add]
    congr 2
    omega
  have hpj : ((p ^ j).totient : ℝ) ≠ 0 := by
    exact_mod_cast totient_ne_zero_of_ne_zero (pow_ne_zero j hp.ne_zero)
  rw [vonMangoldt_apply_pow hj.ne', vonMangoldt_apply_prime hp,
    Nat.totient_mul (Nat.Coprime.pow_left v hcop), hphi]
  have e : ((p ^ j).totient : ℝ) * (Real.log p / ((p ^ j).totient : ℝ)) = Real.log p := by
    first
    | rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hpj, mul_one]
    | field_simp
  push_cast
  linear_combination (-((p : ℝ) ^ (v - j) * (M.totient : ℝ))) * e

variable {N : ℕ} [NeZero N]

/- English proof (translation)
Use `first`. Consider the case `exact ZMod.natCast_zmod_val x`. Consider the case `simp`.
-/
private theorem natCast_val_zmod_eq_self (x : ZMod N) : ((x.val : ℕ) : ZMod N) = x := by
  first
  | exact ZMod.natCast_zmod_val x
  | simp

/- English proof (translation)
Use `first`. Consider the case `exact CharP.intCast_eq_zero_iff (ZMod N) N a`. Consider the case `exact ZMod.intCast_zmod_eq_zero_iff_dvd a N`.
-/
private theorem intCast_zmod_eq_zero_iff_dvd' (a : ℤ) : ((a : ZMod N) = 0) ↔ (N : ℤ) ∣ a := by
  first
  | exact CharP.intCast_eq_zero_iff (ZMod N) N a
  | exact ZMod.intCast_zmod_eq_zero_iff_dvd a N

/- English proof (translation)
Take `⟨d, hd⟩` from `hm`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `NeZero.ne N (by rw [hd, zero_mul])`. Establish `hdm : N / m = d`.

Rewrite using `[hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]`. Establish `key : m • (u - 1) = (((m : ℤ) * ((u.val : ℤ) - 1) : ℤ) : ZMod N)`. Rewrite using `[nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_one, natCast_val_zmod_eq_self]`. Establish `hN : (N : ℤ) = (m : ℤ) * d` using `by exact_mod_cast hd`. Rewrite using `[hdm, addOrderOf_dvd_iff_nsmul_eq_zero, key, intCast_zmod_eq_zero_iff_dvd', hN, mul_dvd_mul_iff_left (by exact_mod_cast hm0), Nat.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm]`.
-/
theorem order_dvd_iff {m : ℕ} (hm : m ∣ N) (u : ZMod N) : addOrderOf (u - 1) ∣ m ↔ u.val ≡ 1 [MOD N / m] := by
  obtain ⟨d, hd⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by rw [hd, zero_mul])
  have hdm : N / m = d := by
    rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]
  have key : m • (u - 1) = (((m : ℤ) * ((u.val : ℤ) - 1) : ℤ) : ZMod N) := by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_one,
      natCast_val_zmod_eq_self]
  have hN : (N : ℤ) = (m : ℤ) * d := by exact_mod_cast hd
  rw [hdm, addOrderOf_dvd_iff_nsmul_eq_zero, key, intCast_zmod_eq_zero_iff_dvd', hN,
    mul_dvd_mul_iff_left (by exact_mod_cast hm0), Nat.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm]

/- English proof (translation)
Rewrite using `[← ZMod.cast_eq_val]`. Use `first`. Consider the case `rfl`. Consider the case `exact ZMod.unitsMap_val hd u`. Consider the case `simp [ZMod.unitsMap_def]`.
-/
private theorem coe_unitsMap_eq_natCast_val_of_dvd {d : ℕ} (hd : d ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap hd u : (ZMod d)ˣ) : ZMod d) = (((u : ZMod N).val : ℕ) : ZMod d) := by
  rw [← ZMod.cast_eq_val]
  first
  | rfl
  | exact ZMod.unitsMap_val hd u
  | simp [ZMod.unitsMap_def]

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, coe_unitsMap_eq_natCast_val_of_dvd, Units.val_one, ← Nat.cast_one (R := ZMod f), ZMod.natCast_eq_natCast_iff]`.
-/
theorem mem_ker_iff {f : ℕ} (hf : f ∣ N) (u : (ZMod N)ˣ) :
    u ∈ (ZMod.unitsMap hf).ker ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  rw [MonoidHom.mem_ker, Units.ext_iff, coe_unitsMap_eq_natCast_val_of_dvd, Units.val_one, ← Nat.cast_one (R := ZMod f),
    ZMod.natCast_eq_natCast_iff]

def KK (N : ℕ) [NeZero N] (f : ℕ) : Finset (ZMod N)ˣ := univ.filter fun u => (u : ZMod N).val ≡ 1 [MOD f]

/- English proof (translation)
Simplify using `[KK]`.
-/
theorem mem_KK {f : ℕ} {u : (ZMod N)ˣ} : u ∈ KK N f ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  simp [KK]

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `NeZero.ne N (zero_dvd_iff.mp hf)`.
-/
private theorem ne_zero_of_dvd_of_neZero {f : ℕ} (hf : f ∣ N) : f ≠ 0 := by
  rintro rfl
  exact NeZero.ne N (zero_dvd_iff.mp hf)

/- English proof (translation)
The claim follows from `addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])`.
-/
private theorem addOrderOf_dvd_of_zmod (x : ZMod N) : addOrderOf x ∣ N :=
  addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])

/- English proof (translation)
Use `haveI : NeZero f := ⟨ne_zero_of_dvd_of_neZero hf⟩`. Establish `h1 : (KK N f).card = Nat.card (ZMod.unitsMap hf).ker`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `(Fintype.card_of_subtype (p := fun u => u ∈ (ZMod.unitsMap hf).ker) _ fun u => by rw [mem_KK, mem_ker_iff hf]).symm`. Establish `h2 : (ZMod.unitsMap hf).ker.index = Nat.card (ZMod f)ˣ` using `by first`.

Consider the case `exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hf)).toEquiv`. Consider the case `rw [Subgroup.index_ker, Set.range_eq_univ.mpr (ZMod.unitsMap_surjective hf), Nat.card_univ]`. Rewrite using `[h1, ← ZMod.card_units_eq_totient f, ← Nat.card_eq_fintype_card, ← h2, Subgroup.card_mul_index, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`.
-/
theorem card_KK {f : ℕ} (hf : f ∣ N) : (KK N f).card * f.totient = N.totient := by
  classical
  haveI : NeZero f := ⟨ne_zero_of_dvd_of_neZero hf⟩
  have h1 : (KK N f).card = Nat.card (ZMod.unitsMap hf).ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_of_subtype (p := fun u => u ∈ (ZMod.unitsMap hf).ker) _
      fun u => by rw [mem_KK, mem_ker_iff hf]).symm
  have h2 : (ZMod.unitsMap hf).ker.index = Nat.card (ZMod f)ˣ := by
    first
    | exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hf)).toEquiv
    | rw [Subgroup.index_ker, Set.range_eq_univ.mpr (ZMod.unitsMap_surjective hf), Nat.card_univ]
  rw [h1, ← ZMod.card_units_eq_totient f, ← Nat.card_eq_fintype_card, ← h2, Subgroup.card_mul_index,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

open Classical in

def rho (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ℝ :=
  (((KK N f).filter fun u => u ∉ U).card : ℝ) * f.totient / N.totient

open Classical in
/- English proof (translation)
Establish `hN : N ≠ 0` using `NeZero.ne N`. Establish `hT : (N.totient : ℝ) ≠ 0` using `by exact_mod_cast totient_ne_zero_of_ne_zero hN`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Rewrite `hu` using `[Finset.mem_filter]`.

Establish `hd : addOrderOf ((u : ZMod N) - 1) ∣ N` using `addOrderOf_dvd_of_zmod _`. Establish `h1 : addOrderOf ((u : ZMod N) - 1) ≠ 1`. Introduce `h`. Establish `h'` using `addOrderOf_nsmul_eq_zero ((u : ZMod N) - 1)`. Rewrite `h'` using `[h, one_nsmul, sub_eq_zero]`.

Conclude with `hu.2 (by rw [show u = 1 from Units.ext (by rw [h', Units.val_one])]; exact one_mem U)`. Rewrite using `[← Finset.sum_filter, ← Finset.sum_div, weight_sum hN hd h1, eq_div_iff hT]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ m ∈ N.divisors, ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U), (if addOrderOf ((u : ZMod N) - 1) ∣ m then vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := Finset.sum_comm`. Use `_ = _ := by`.

Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hmN : m ∣ N` using `Nat.dvd_of_mem_divisors hm`. Establish `hcard : (((univ : Finset (ZMod N)ˣ).filter (fun u : (ZMod N)ˣ => u ∉ U)).filter (fun u : (ZMod N)ˣ => addOrderOf ((u : ZMod N) - 1) ∣ m)).card = ((KK N (N / m)).filter fun u => u ∉ U).card`. Apply `congrArg Finset.card` to reduce the goal to its premises. Use extensionality with `u`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, mem_KK, order_dvd_iff hmN]`. The claim follows by propositional logic. Rewrite using `[← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]`. Unfold `rho`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abel (U : Subgroup (ZMod N)ˣ) :
    ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) =
      ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hT : (N.totient : ℝ) ≠ 0 := by exact_mod_cast totient_ne_zero_of_ne_zero hN
  calc _ = ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        ∑ m ∈ N.divisors, (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.mem_filter] at hu
        have hd : addOrderOf ((u : ZMod N) - 1) ∣ N := addOrderOf_dvd_of_zmod _
        have h1 : addOrderOf ((u : ZMod N) - 1) ≠ 1 := by
          intro h
          have h' := addOrderOf_nsmul_eq_zero ((u : ZMod N) - 1)
          rw [h, one_nsmul, sub_eq_zero] at h'
          exact hu.2 (by rw [show u = 1 from Units.ext (by rw [h', Units.val_one])]; exact one_mem U)
        rw [← Finset.sum_filter, ← Finset.sum_div, weight_sum hN hd h1, eq_div_iff hT]
        ring
    _ = ∑ m ∈ N.divisors, ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmN : m ∣ N := Nat.dvd_of_mem_divisors hm
        have hcard : (((univ : Finset (ZMod N)ˣ).filter (fun u : (ZMod N)ˣ => u ∉ U)).filter
            (fun u : (ZMod N)ˣ => addOrderOf ((u : ZMod N) - 1) ∣ m)).card =
            ((KK N (N / m)).filter fun u => u ∉ U).card := by
          apply congrArg Finset.card
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_KK,
            order_dvd_iff hmN]
          tauto
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
        unfold rho
        ring

/- English proof (translation)
Introduce `h`. Establish `h'` using `card_KK hf`. Rewrite `h'` using `[h, zero_mul]`. Conclude with `totient_ne_zero_of_ne_zero (NeZero.ne N) h'.symm`.
-/
private theorem card_KK_ne_zero_of_dvd {f : ℕ} (hf : f ∣ N) : (KK N f).card ≠ 0 := by
  intro h
  have h' := card_KK hf
  rw [h, zero_mul] at h'
  exact totient_ne_zero_of_ne_zero (NeZero.ne N) h'.symm

/- English proof (translation)
Unfold `rho`. Check the signs of the components of the expression.
-/
theorem rho_nonneg (U : Subgroup (ZMod N)ˣ) (f : ℕ) : 0 ≤ rho U f := by
  unfold rho
  positivity

open Classical in
/- English proof (translation)
Establish `card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ((KK N f).filter fun u => u ∉ U).card + ((KK N f).filter fun u => u ∈ U).card = (KK N f).card`. Rewrite using `[add_comm]`. Use `first`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`. Consider the case `convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)`.

Consider the case `convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)`. Establish `kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f = (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card`. Establish `hc : ((KK N f).card : ℝ) * f.totient = N.totient`. Conclude with `card_KK hf` after adjusting the coercions. Establish `ht : (f.totient : ℝ) ≠ 0`.

Conclude with `totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)` after adjusting the coercions. Unfold `rho`. Rewrite using `[← hc, mul_div_mul_right _ _ ht]`. Establish `hc : ((KK N f).card : ℝ) * f.totient = N.totient`. Conclude with `card_KK hf` after adjusting the coercions.

Establish `ht : (f.totient : ℝ) ≠ 0`. Conclude with `totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)` after adjusting the coercions. Establish `hK : ((KK N f).card : ℝ) ≠ 0` using `by exact_mod_cast card_KK_ne_zero_of_dvd hf`. Establish `hs : (((KK N f).filter fun u => u ∉ U).card : ℝ) + (((KK N f).filter fun u => u ∈ U).card : ℝ) = (KK N f).card`. Conclude with `card_outside_add_card_inside_lemma_12 U f` after adjusting the coercions.

Rewrite using `[kernelOutsideFraction_eq_div_lemma_13 U hf, ← hc, mul_div_mul_right _ _ ht, eq_sub_iff_add_eq, ← add_div, hs, div_self hK]`.
-/
theorem rho_eq (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
    rho U f = 1 - (((KK N f).filter fun u => u ∈ U).card : ℝ) * f.totient / N.totient := by
  have card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
      ((KK N f).filter fun u => u ∉ U).card +
        ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    rw [add_comm]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)
    | convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)
  have kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      rho U f =
        (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
    have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
      exact_mod_cast card_KK hf
    have ht : (f.totient : ℝ) ≠ 0 := by
      exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
    unfold rho
    rw [← hc, mul_div_mul_right _ _ ht]
  have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
    exact_mod_cast card_KK hf
  have ht : (f.totient : ℝ) ≠ 0 := by
    exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
  have hK : ((KK N f).card : ℝ) ≠ 0 := by exact_mod_cast card_KK_ne_zero_of_dvd hf
  have hs : (((KK N f).filter fun u => u ∉ U).card : ℝ) +
      (((KK N f).filter fun u => u ∈ U).card : ℝ) = (KK N f).card := by
    exact_mod_cast card_outside_add_card_inside_lemma_12 U f
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf, ← hc, mul_div_mul_right _ _ ht, eq_sub_iff_add_eq, ← add_div, hs,
    div_self hK]

/- English proof (translation)
Rewrite using `[mem_KK, mem_ker_iff hf]`.
-/
private theorem mem_KK_iff_mem_ker_unitsMap {f : ℕ} (hf : f ∣ N) {u : (ZMod N)ˣ} :
    u ∈ KK N f ↔ u ∈ (ZMod.unitsMap hf).ker := by
  rw [mem_KK, mem_ker_iff hf]

/- English proof (translation)
Rewrite using `[mem_KK_iff_mem_ker_unitsMap hf]`. Conclude with `one_mem _`.
-/
theorem one_mem_KK {f : ℕ} (hf : f ∣ N) : (1 : (ZMod N)ˣ) ∈ KK N f := by
  rw [mem_KK_iff_mem_ker_unitsMap hf]
  exact one_mem _

/- English proof (translation)
Rewrite `hu`, `hv`, the goal using `[mem_KK_iff_mem_ker_unitsMap hf]`. Conclude with `mul_mem hu hv`.
-/
theorem mul_mem_KK {f : ℕ} (hf : f ∣ N) {u v : (ZMod N)ˣ} (hu : u ∈ KK N f) (hv : v ∈ KK N f) : u * v ∈ KK N f := by
  rw [mem_KK_iff_mem_ker_unitsMap hf] at hu hv ⊢
  exact mul_mem hu hv

/- English proof (translation)
Use `open Classical in`. Establish `one_le_card_inside_lemma_14 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : (1 : ℝ) ≤ (((KK N f).filter fun u => u ∈ U).card : ℝ)`. Establish `h : 0 < ((KK N f).filter fun u => u ∈ U).card` using `Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨one_mem_KK hf, one_mem U⟩⟩`. Conclude with `h` after adjusting the coercions. Rewrite using `[rho_eq U hf, mul_div_assoc]`.

Establish `hB` using `one_le_card_inside_lemma_14 U hf`. Establish `h0 : (0 : ℝ) ≤ (f.totient : ℝ) / N.totient` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rho_le (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f ≤ 1 - (f.totient : ℝ) / N.totient := by
  open Classical in
  have one_le_card_inside_lemma_14 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      (1 : ℝ) ≤ (((KK N f).filter fun u => u ∈ U).card : ℝ) := by
    have h : 0 < ((KK N f).filter fun u => u ∈ U).card :=
      Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨one_mem_KK hf, one_mem U⟩⟩
    exact_mod_cast h
  rw [rho_eq U hf, mul_div_assoc]
  have hB := one_le_card_inside_lemma_14 U hf
  have h0 : (0 : ℝ) ≤ (f.totient : ℝ) / N.totient := by positivity
  nlinarith

/- English proof (translation)
Use `open Classical in`. Establish `card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ((KK N f).filter fun u => u ∉ U).card + ((KK N f).filter fun u => u ∈ U).card = (KK N f).card`. Rewrite using `[add_comm]`. Use `first`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`.

Consider the case `convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)`. Consider the case `convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)`. Use `open Classical in`. Establish `kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f = (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card`. Establish `hc : ((KK N f).card : ℝ) * f.totient = N.totient`.

Conclude with `card_KK hf` after adjusting the coercions. Establish `ht : (f.totient : ℝ) ≠ 0`. Conclude with `totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)` after adjusting the coercions. Unfold `rho`. Rewrite using `[← hc, mul_div_mul_right _ _ ht]`.

Use `open Classical in`. Establish `card_inside_le_outside_lemma_15 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) {u0 : (ZMod N)ˣ} (hu0 : u0 ∈ KK N f) (hu0' : u0 ∉ U) : ((KK N f).filter fun u => u ∈ U).card ≤ ((KK N f).filter fun u => u ∉ U).card`. Apply `Finset.card_le_card_of_injOn (fun v => u0 * v)` to reduce the goal to its premises. Introduce `v hv`. Simplify using `only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢`.

Use `⟨mul_mem_KK hf hu0 hv.1, fun h => hu0' ?_⟩` and prove the remaining obligations. Establish `h'` using `mul_mem h (inv_mem hv.2)`. Rewrite `h'` using `[mul_inv_cancel_right]`. Then use the resulting hypothesis. Introduce `a _ b _ hab`. Conclude with `mul_left_cancel hab`.

Take `⟨u0, hu0, hu0'⟩` from `h`. Establish `h1` using `(Nat.cast_le (α := ℝ)).mpr (card_inside_le_outside_lemma_15 U hf hu0 hu0')`. Establish `h2` using `congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)`. Move the coercions through the operations in `at h2`. Establish `hK : (0 : ℝ) < (KK N f).card` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))`.

Rewrite using `[kernelOutsideFraction_eq_div_lemma_13 U hf]`. Use `first`. Consider the case `exact (le_div_iff₀ hK).mpr (by linarith)`. Consider the case `exact (le_div_iff hK).mpr (by linarith)`.
-/
theorem half_le_rho (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) (h : ∃ u ∈ KK N f, u ∉ U) : 1 / 2 ≤ rho U f := by
  open Classical in
  have card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
      ((KK N f).filter fun u => u ∉ U).card +
        ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    rw [add_comm]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)
    | convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)
  open Classical in
  have kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      rho U f =
        (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
    have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
      exact_mod_cast card_KK hf
    have ht : (f.totient : ℝ) ≠ 0 := by
      exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
    unfold rho
    rw [← hc, mul_div_mul_right _ _ ht]
  open Classical in
  have card_inside_le_outside_lemma_15 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) {u0 : (ZMod N)ˣ}
      (hu0 : u0 ∈ KK N f) (hu0' : u0 ∉ U) :
      ((KK N f).filter fun u => u ∈ U).card ≤
        ((KK N f).filter fun u => u ∉ U).card := by
    apply Finset.card_le_card_of_injOn (fun v => u0 * v)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢
      refine ⟨mul_mem_KK hf hu0 hv.1, fun h => hu0' ?_⟩
      have h' := mul_mem h (inv_mem hv.2)
      rwa [mul_inv_cancel_right] at h'
    · intro a _ b _ hab
      exact mul_left_cancel hab
  obtain ⟨u0, hu0, hu0'⟩ := h
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_inside_le_outside_lemma_15 U hf hu0 hu0')
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)
  push_cast at h2
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf]
  first
  | exact (le_div_iff₀ hK).mpr (by linarith)
  | exact (le_div_iff hK).mpr (by linarith)

/- English proof (translation)
Use `open Classical in`. Establish `card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) : ((KK N f).filter fun u => u ∉ U).card + ((KK N f).filter fun u => u ∈ U).card = (KK N f).card`. Rewrite using `[add_comm]`. Use `first`. Consider the case `exact Finset.filter_card_add_filter_neg_card_eq_card _`.

Consider the case `convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)`. Consider the case `convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)`. Use `open Classical in`. Establish `kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) : rho U f = (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card`. Establish `hc : ((KK N f).card : ℝ) * f.totient = N.totient`.

Conclude with `card_KK hf` after adjusting the coercions. Establish `ht : (f.totient : ℝ) ≠ 0`. Conclude with `totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)` after adjusting the coercions. Unfold `rho`. Rewrite using `[← hc, mul_div_mul_right _ _ ht]`.

Use `open Classical in`. Establish `card_outside_le_inside_lemma_16 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) : ((KK N f).filter fun u => u ∉ U).card ≤ ((KK N f).filter fun u => u ∈ U).card`. Break down `Finset.eq_empty_or_nonempty ((KK N f).filter fun u => u ∉ U) with he | ⟨u0, hu0⟩` into its components or cases. Rewrite using `[he, Finset.card_empty]`. Conclude with `Nat.zero_le _`.

Rewrite `hu0` using `[Finset.mem_filter]`. Apply `Finset.card_le_card_of_injOn (fun v => u0 * v)` to reduce the goal to its premises. Introduce `v hv`. Simplify using `only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢`. Conclude with `⟨mul_mem_KK hf hu0.1 hv.1, h u0 hu0.1 v hv.1 hu0.2 hv.2⟩`.

Introduce `a _ b _ hab`. Conclude with `mul_left_cancel hab`. Establish `h1` using `(Nat.cast_le (α := ℝ)).mpr (card_outside_le_inside_lemma_16 U hf h)`. Establish `h2` using `congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)`. Move the coercions through the operations in `at h2`.

Establish `hK : (0 : ℝ) < (KK N f).card` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))`. Rewrite using `[kernelOutsideFraction_eq_div_lemma_13 U hf]`. Use `first`. Consider the case `exact (div_le_iff₀ hK).mpr (by linarith)`. Consider the case `exact (div_le_iff hK).mpr (by linarith)`.
-/
theorem rho_le_half (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
    (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) : rho U f ≤ 1 / 2 := by
  open Classical in
  have card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
      ((KK N f).filter fun u => u ∉ U).card +
        ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    rw [add_comm]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)
    | convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)
  open Classical in
  have kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      rho U f =
        (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
    have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
      exact_mod_cast card_KK hf
    have ht : (f.totient : ℝ) ≠ 0 := by
      exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
    unfold rho
    rw [← hc, mul_div_mul_right _ _ ht]
  open Classical in
  have card_outside_le_inside_lemma_16 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
      (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) :
      ((KK N f).filter fun u => u ∉ U).card ≤
        ((KK N f).filter fun u => u ∈ U).card := by
    rcases Finset.eq_empty_or_nonempty ((KK N f).filter fun u => u ∉ U) with he | ⟨u0, hu0⟩
    · rw [he, Finset.card_empty]
      exact Nat.zero_le _
    · rw [Finset.mem_filter] at hu0
      apply Finset.card_le_card_of_injOn (fun v => u0 * v)
      · intro v hv
        simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢
        exact ⟨mul_mem_KK hf hu0.1 hv.1, h u0 hu0.1 v hv.1 hu0.2 hv.2⟩
      · intro a _ b _ hab
        exact mul_left_cancel hab
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_outside_le_inside_lemma_16 U hf h)
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)
  push_cast at h2
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf]
  first
  | exact (div_le_iff₀ hK).mpr (by linarith)
  | exact (div_le_iff hK).mpr (by linarith)

/- English proof (translation)
Introduce `u hu`. Rewrite `hu` using `[mem_KK]`. Establish `hL : Nat.lcm a b ∣ N` using `Nat.lcm_dvd ha hb`. Take `⟨k, hka, hkb⟩` from `Nat.chineseRemainder' (hu.symm : 1 ≡ (u : ZMod N).val [MOD Nat.gcd a b])`. Establish `hca : Nat.Coprime k a`.

Unfold `Nat.Coprime`. Rewrite using `[hka.gcd_eq, Nat.gcd_one_left]`. Establish `hub : Nat.Coprime (u : ZMod N).val b` using `Nat.Coprime.coprime_dvd_right hb (ZMod.val_coe_unit_coprime u)`. Establish `hcb : Nat.Coprime k b`. Unfold `Nat.Coprime`.

Rewrite using `[hkb.gcd_eq]`. Conclude with `hub`. Establish `hcop : Nat.Coprime k (Nat.lcm a b)` using `Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul a b) (Nat.Coprime.mul_right hca hcb)`. Take `⟨v, hv⟩` from `ZMod.unitsMap_surjective hL (ZMod.unitOfCoprime k hcop)`. Establish `hvk : (v : ZMod N).val ≡ k [MOD Nat.lcm a b]`.

Establish `h3` using `congrArg (fun w : (ZMod (Nat.lcm a b))ˣ => (w : ZMod (Nat.lcm a b))) hv`. Simplify using `only [ZMod.coe_unitOfCoprime] at h3`. Rewrite `h3` using `[coe_unitsMap_eq_natCast_val_of_dvd]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mp h3`. Establish `hva : v ∈ U` using `h1 v (by`.

Rewrite using `[mem_KK]`. Conclude with `(hvk.of_dvd (Nat.dvd_lcm_left a b)).trans hka)`. Establish `hvb : v⁻¹ * u ∈ U` using `h2 _ (by`. Rewrite using `[mem_KK_iff_mem_ker_unitsMap hb, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[coe_unitsMap_eq_natCast_val_of_dvd, coe_unitsMap_eq_natCast_val_of_dvd, ZMod.natCast_eq_natCast_iff]`. Conclude with `(hvk.of_dvd (Nat.dvd_lcm_right a b)).trans hkb)`. Establish `h4` using `mul_mem hva hvb`. Rewrite `h4` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem KK_gcd (U : Subgroup (ZMod N)ˣ) {a b : ℕ} (ha : a ∣ N) (hb : b ∣ N) (h1 : ∀ u ∈ KK N a, u ∈ U)
    (h2 : ∀ u ∈ KK N b, u ∈ U) : ∀ u ∈ KK N (Nat.gcd a b), u ∈ U := by
  intro u hu
  rw [mem_KK] at hu
  have hL : Nat.lcm a b ∣ N := Nat.lcm_dvd ha hb
  obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder' (hu.symm : 1 ≡ (u : ZMod N).val [MOD Nat.gcd a b])
  have hca : Nat.Coprime k a := by
    unfold Nat.Coprime
    rw [hka.gcd_eq, Nat.gcd_one_left]
  have hub : Nat.Coprime (u : ZMod N).val b :=
    Nat.Coprime.coprime_dvd_right hb (ZMod.val_coe_unit_coprime u)
  have hcb : Nat.Coprime k b := by
    unfold Nat.Coprime
    rw [hkb.gcd_eq]
    exact hub
  have hcop : Nat.Coprime k (Nat.lcm a b) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul a b) (Nat.Coprime.mul_right hca hcb)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hL (ZMod.unitOfCoprime k hcop)
  have hvk : (v : ZMod N).val ≡ k [MOD Nat.lcm a b] := by
    have h3 := congrArg (fun w : (ZMod (Nat.lcm a b))ˣ => (w : ZMod (Nat.lcm a b))) hv
    simp only [ZMod.coe_unitOfCoprime] at h3
    rw [coe_unitsMap_eq_natCast_val_of_dvd] at h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
  have hva : v ∈ U := h1 v (by
    rw [mem_KK]
    exact (hvk.of_dvd (Nat.dvd_lcm_left a b)).trans hka)
  have hvb : v⁻¹ * u ∈ U := h2 _ (by
    rw [mem_KK_iff_mem_ker_unitsMap hb, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    rw [coe_unitsMap_eq_natCast_val_of_dvd, coe_unitsMap_eq_natCast_val_of_dvd, ZMod.natCast_eq_natCast_iff]
    exact (hvk.of_dvd (Nat.dvd_lcm_right a b)).trans hkb)
  have h4 := mul_mem hva hvb
  rwa [mul_inv_cancel_left] at h4

end Formalism.HC.Der.Rd

end
