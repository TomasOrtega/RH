import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.ValMax

variable {Ω : Type} [Field Ω]

/- English proof (translation)
The claim follows from `V.valuation_le_one ⟨_, intCast_mem V z⟩`.
-/
theorem val_int_le_one (V : ValuationSubring Ω) (z : ℤ) : V.valuation (z : Ω) ≤ 1 :=
  V.valuation_le_one ⟨_, intCast_mem V z⟩

/- English proof (translation)
Establish `hc : IsCoprime (q : ℤ) n` using `Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)`. Take `⟨a, b, hab⟩` from `hc`. Establish `h1 : (a : Ω) * (q : Ω) + (b : Ω) * (n : Ω) = 1`. Use `congrArg (Int.cast : ℤ → Ω) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hle : V.valuation (n : Ω) ≤ 1` using `by simpa using val_int_le_one V (n : ℤ)`. Assume the negation of the conclusion as `hne`. Establish `hlt : V.valuation (n : Ω) < 1` using `lt_of_le_of_ne hle hne`. Establish `ha : V.valuation ((a : Ω) * (q : Ω)) < 1`.

Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V a)) hV`. Establish `hb : V.valuation ((b : Ω) * (n : Ω)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V b)) hlt`.

Use `V.valuation.map_add_lt ha hb` as an intermediate fact. Rewrite `this` using `[h1, map_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem val_nat_eq_one (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : ¬ q ∣ n) : V.valuation (n : Ω) = 1 := by
  have hc : IsCoprime (q : ℤ) n :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : Ω) * (q : Ω) + (b : Ω) * (n : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) hab
    push_cast at this
    exact this
  have hle : V.valuation (n : Ω) ≤ 1 := by simpa using val_int_le_one V (n : ℤ)
  by_contra hne
  have hlt : V.valuation (n : Ω) < 1 := lt_of_le_of_ne hle hne
  have ha : V.valuation ((a : Ω) * (q : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V a)) hV
  have hb : V.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_int_le_one V b)) hlt
  have := V.valuation.map_add_lt ha hb
  rw [h1, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Take `⟨e, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one`. Use `⟨e, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[map_mul, map_pow, val_nat_eq_one V hq hV hm, mul_one]`.
-/
theorem val_nat_eq_pow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, V.valuation (n : Ω) = V.valuation (q : Ω) ^ e := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  refine ⟨e, ?_⟩
  push_cast
  rw [map_mul, map_pow, val_nat_eq_one V hq hV hm, mul_one]

variable [Algebra ℚ Ω]

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `Nat.cast_ne_zero.2 hq.ne_zero`.
-/
theorem val_q_ne_zero (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime) :
    V.valuation (q : Ω) ≠ 0 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rw [Valuation.ne_zero_iff]
  exact Nat.cast_ne_zero.2 hq.ne_zero

/- English proof (translation)
Establish `h0` using `val_q_ne_zero V hq`. Take `⟨e1, h1⟩` from `val_nat_eq_pow V hq hV (n := r.num.natAbs) (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr))`. Take `⟨e2, h2⟩` from `val_nat_eq_pow V hq hV (n := r.den) r.den_nz`. Establish `h3 : V.valuation ((r.num : ℤ) : Ω) = V.valuation (q : Ω) ^ e1`. Rewrite using `[← h1]`.

Break down `Int.natAbs_eq r.num with h | h` into its components or cases. Use `conv_lhs => rw [h]`. Simplify using `only [Int.cast_natCast]`. Use `conv_lhs => rw [h]`. Simplify using `only [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]`.

Use `⟨(e1 : ℤ) - e2, ?_⟩` and prove the remaining obligations. Establish `h4 : algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) / ((r.den : ℕ) : Ω)` using `by conv_lhs => rw [← Rat.num_div_den r]`. Rewrite using `[map_div₀, map_intCast, map_natCast]`. Rewrite using `[h4, map_div₀, h3, h2, zpow_sub₀ h0, zpow_natCast, zpow_natCast]`.
-/
theorem val_rat_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {r : ℚ} (hr : r ≠ 0) :
    ∃ e : ℤ, V.valuation (algebraMap ℚ Ω r) = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_nat_eq_pow V hq hV (n := r.num.natAbs)
    (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hr))
  obtain ⟨e2, h2⟩ := val_nat_eq_pow V hq hV (n := r.den) r.den_nz
  have h3 : V.valuation ((r.num : ℤ) : Ω) = V.valuation (q : Ω) ^ e1 := by
    rw [← h1]
    rcases Int.natAbs_eq r.num with h | h
    · conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    · conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]
  refine ⟨(e1 : ℤ) - e2, ?_⟩
  have h4 : algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) / ((r.den : ℕ) : Ω) := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, map_intCast, map_natCast]
  rw [h4, map_div₀, h3, h2, zpow_sub₀ h0, zpow_natCast, zpow_natCast]

/- English proof (translation)
Establish `h0` using `val_q_ne_zero V hq`. Take `⟨e1, h1⟩` from `val_rat_eq_zpow V hq hV hr`. Take `⟨e2, h2⟩` from `val_rat_eq_zpow V hq hV hs`. Establish `hx0 : V.valuation x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Rewrite `h` using `[Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, h1, h2, map_pow, map_pow, pow_add, mul_comm (V.valuation x ^ i), ← mul_assoc]`.

Establish `h3` using `mul_right_cancel₀ (pow_ne_zero i hx0) h`. Use `⟨e1 - e2, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_sub₀ h0, h3, mul_div_cancel_left₀ _ (zpow_ne_zero _ h0)]`.
-/
theorem val_pow_sub (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) {r s : ℚ} (hr : r ≠ 0) (hs : s ≠ 0)
    {i k : ℕ} (h : V.valuation (r • x ^ i) = V.valuation (s • x ^ (i + k))) :
    ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  have h0 := val_q_ne_zero V hq
  obtain ⟨e1, h1⟩ := val_rat_eq_zpow V hq hV hr
  obtain ⟨e2, h2⟩ := val_rat_eq_zpow V hq hV hs
  have hx0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, h1, h2, map_pow, map_pow, pow_add,
    mul_comm (V.valuation x ^ i), ← mul_assoc] at h
  have h3 := mul_right_cancel₀ (pow_ne_zero i hx0) h
  refine ⟨e1 - e2, ?_⟩
  rw [zpow_sub₀ h0, h3, mul_div_cancel_left₀ _ (zpow_ne_zero _ h0)]

/- English proof (translation)
Use `set p := minpoly ℚ x with hp`. Use `set f : ℕ → Ω := fun i => p.coeff i • x ^ i with hf`. Establish `hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0`. Rewrite using `[← Polynomial.aeval_eq_sum_range]`. Conclude with `minpoly.aeval ℚ x`.

Take `⟨j, hj, hmax⟩` from `Finset.exists_max_image (Finset.range (p.natDegree + 1)) (fun i => V.valuation (f i)) ⟨0, by simp⟩`. Establish `hj0 : V.valuation (f j) ≠ 0`. Introduce `h`. Establish `h1` using `hmax p.natDegree (by simp)`. Establish `h2 : f p.natDegree = x ^ p.natDegree`.

Establish `: p.coeff p.natDegree = 1` using `(minpoly.monic hi).coeff_natDegree`. Simplify using `only [hf, this, one_smul]`. Rewrite `h1` using `[h, h2, le_zero_iff, Valuation.zero_iff]`. Conclude with `pow_ne_zero _ hx h1`. Establish `hex : ∃ i ∈ Finset.range (p.natDegree + 1) \ {j}, ¬ V.valuation (f i) < V.valuation (f j)`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `V.valuation.map_sum_eq_of_lt hj hcon` as an intermediate fact. Rewrite `this` using `[hsum, map_zero]`. Conclude with `hj0 this.symm`.

Take `⟨i, hi', hlt⟩` from `hex`. Rewrite `hi'` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Establish `heq : V.valuation (f i) = V.valuation (f j)` using `le_antisymm (hmax i hi'.1) (not_lt.1 hlt)`. Establish `hcj : p.coeff j ≠ 0`. Introduce `h`.

Apply `hj0` to reduce the goal to its premises. Simplify using `only [hf, h, zero_smul, map_zero]`. Establish `hci : p.coeff i ≠ 0`. Introduce `h`. Apply `hj0` to reduce the goal to its premises.

Rewrite using `[← heq]`. Simplify using `only [hf, h, zero_smul, map_zero]`. Establish `hi1` using `Finset.mem_range.1 hi'.1`. Establish `hj1` using `Finset.mem_range.1 hj`. Break down `lt_or_gt_of_ne hi'.2 with hij | hij` into its components or cases.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hij.le`. Conclude with `⟨k, by omega, by omega, val_pow_sub V hq hV hx hci hcj heq⟩`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hij.le`. Conclude with `⟨k, by omega, by omega, val_pow_sub V hq hV hx hcj hci heq.symm⟩`.
-/
theorem val_pow_eq_zpow (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) :
    ∃ k : ℕ, 0 < k ∧ k ≤ (minpoly ℚ x).natDegree ∧
      ∃ e : ℤ, V.valuation x ^ k = V.valuation (q : Ω) ^ e := by
  classical
  set p := minpoly ℚ x with hp
  set f : ℕ → Ω := fun i => p.coeff i • x ^ i with hf
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), f i = 0 := by
    rw [← Polynomial.aeval_eq_sum_range]
    exact minpoly.aeval ℚ x
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range (p.natDegree + 1))
    (fun i => V.valuation (f i)) ⟨0, by simp⟩
  have hj0 : V.valuation (f j) ≠ 0 := by
    intro h
    have h1 := hmax p.natDegree (by simp)
    have h2 : f p.natDegree = x ^ p.natDegree := by
      have : p.coeff p.natDegree = 1 := (minpoly.monic hi).coeff_natDegree
      simp only [hf, this, one_smul]
    rw [h, h2, le_zero_iff, Valuation.zero_iff] at h1
    exact pow_ne_zero _ hx h1
  have hex : ∃ i ∈ Finset.range (p.natDegree + 1) \ {j}, ¬ V.valuation (f i) < V.valuation (f j) := by
    by_contra hcon
    push Not at hcon
    have := V.valuation.map_sum_eq_of_lt hj hcon
    rw [hsum, map_zero] at this
    exact hj0 this.symm
  obtain ⟨i, hi', hlt⟩ := hex
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi'
  have heq : V.valuation (f i) = V.valuation (f j) :=
    le_antisymm (hmax i hi'.1) (not_lt.1 hlt)
  have hcj : p.coeff j ≠ 0 := by
    intro h
    apply hj0
    simp only [hf, h, zero_smul, map_zero]
  have hci : p.coeff i ≠ 0 := by
    intro h
    apply hj0
    rw [← heq]
    simp only [hf, h, zero_smul, map_zero]
  have hi1 := Finset.mem_range.1 hi'.1
  have hj1 := Finset.mem_range.1 hj
  rcases lt_or_gt_of_ne hi'.2 with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hci hcj heq⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    exact ⟨k, by omega, by omega, val_pow_sub V hq hV hx hcj hci heq.symm⟩

/- English proof (translation)
Take `⟨k, hk0, hk, e, he⟩` from `val_pow_eq_zpow V hq hV hx hi`. Take `⟨m, hm⟩` from `Nat.dvd_factorial hk0 (hk.trans hn)`. Conclude with `⟨e * m, by rw [hm, pow_mul, he, _root_.zpow_mul, zpow_natCast]⟩`.
-/
theorem val_pow_factorial (V : ValuationSubring Ω) {q : ℕ} (hq : q.Prime)
    (hV : V.valuation (q : Ω) < 1) {x : Ω} (hx : x ≠ 0) (hi : IsIntegral ℚ x) {n : ℕ}
    (hn : (minpoly ℚ x).natDegree ≤ n) :
    ∃ e : ℤ, V.valuation x ^ n.factorial = V.valuation (q : Ω) ^ e := by
  obtain ⟨k, hk0, hk, e, he⟩ := val_pow_eq_zpow V hq hV hx hi
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hk0 (hk.trans hn)
  exact ⟨e * m, by rw [hm, pow_mul, he, _root_.zpow_mul, zpow_natCast]⟩

/- English proof (translation)
Establish `h1 : (minpoly K (⟨x, hx⟩ : F)).natDegree ≤ Module.finrank K F` using `minpoly.natDegree_le _`. Rewrite `h1` using `[IntermediateField.minpoly_eq]`. Then use the resulting hypothesis.
-/
theorem natDegree_minpoly_le {K L : Type} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) [FiniteDimensional K F] {x : L} (hx : x ∈ F) :
    (minpoly K x).natDegree ≤ Module.finrank K F := by
  have h1 : (minpoly K (⟨x, hx⟩ : F)).natDegree ≤ Module.finrank K F :=
    minpoly.natDegree_le _
  rwa [IntermediateField.minpoly_eq] at h1

/- English proof (translation)
Introduce `Ω _ _ _ F hF q hq V hV ι a c hc haF hca hex`. Rewrite `hV` using `[ValuationSubring.mem_nonunits_iff]`. Establish `h0` using `val_q_ne_zero V hq`. Establish `hpos : 0 < V.valuation (q : Ω)` using `zero_lt_iff.2 h0`. Establish `hint : ∀ x : Ω, IsIntegral ℚ x` using `fun x => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral`.

Use `set n := Module.finrank ℚ F + (minpoly ℚ c).natDegree with hn`. Take `⟨e0, he0⟩` from `val_pow_factorial V hq hV hc (hint c) (n := n) (by omega)`. Establish `hall : ∀ i, a i ≠ 0 → ∃ e : ℤ, V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e`. Introduce `i hi`. Use `val_pow_factorial V hq hV hi (hint _) ?_` and prove the remaining obligations.

Conclude with `(natDegree_minpoly_le F (haF i)).trans (Nat.le_add_right _ _)`. Take `⟨e, ⟨i, hi, he⟩, hmin⟩` from `Int.exists_least_of_bdd (P := fun e : ℤ => ∃ i, a i ≠ 0 ∧ V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e) ⟨-e0, by`. Introduce and unpack `z ⟨i, -, hz⟩`. Establish `h1 : V.valuation (c * a i) ≤ 1` using `V.valuation_le_one ⟨_, hca i⟩`. Establish `h2 : V.valuation (c * a i) ^ n.factorial ≤ 1` using `pow_le_one' h1 _`.

Rewrite `h2` using `[map_mul, mul_pow, he0, hz, ← zpow_add₀ h0, ← zpow_zero (V.valuation (q : Ω)), zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]`. Use the proof step `omega⟩`. Use the proof step `(by`. Take `⟨i, hi⟩` from `hex`. Take `⟨e, he⟩` from `hall i hi`.

Conclude with `⟨e, i, hi, he⟩)`. Use `⟨i, hi, fun i' => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi' : a i' = 0`. Rewrite using `[hi', map_zero]`. Conclude with `zero_le'`.

Take `⟨e', he'⟩` from `hall i' hi'`. Establish `h1 : V.valuation (a i') ^ n.factorial ≤ V.valuation (a i) ^ n.factorial`. Rewrite using `[he, he', zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]`. Conclude with `hmin e' ⟨i', hi', he'⟩`. Assume the negation of the conclusion as `hcon`.

Conclude with `absurd h1 (not_le.2 (pow_lt_pow_left₀ (not_le.1 hcon) zero_le' n.factorial_ne_zero))`.
-/
theorem exists_max_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (F : IntermediateField ℚ Ω), FiniteDimensional ℚ F → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ (ι : Type) (a : ι → Ω) (c : Ω), c ≠ 0 → (∀ i, a i ∈ F) → (∀ i, c * a i ∈ V) → (∃ i, a i ≠ 0) → ∃ i, a i ≠ 0 ∧ ∀ i', V.valuation (a i') ≤ V.valuation (a i) := by
  intro Ω _ _ _ F hF q hq V hV ι a c hc haF hca hex
  rw [ValuationSubring.mem_nonunits_iff] at hV
  have h0 := val_q_ne_zero V hq
  have hpos : 0 < V.valuation (q : Ω) := zero_lt_iff.2 h0
  have hint : ∀ x : Ω, IsIntegral ℚ x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
  set n := Module.finrank ℚ F + (minpoly ℚ c).natDegree with hn
  obtain ⟨e0, he0⟩ := val_pow_factorial V hq hV hc (hint c) (n := n) (by omega)
  have hall : ∀ i, a i ≠ 0 →
      ∃ e : ℤ, V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e := by
    intro i hi
    refine val_pow_factorial V hq hV hi (hint _) ?_
    exact (natDegree_minpoly_le F (haF i)).trans (Nat.le_add_right _ _)
  obtain ⟨e, ⟨i, hi, he⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun e : ℤ => ∃ i, a i ≠ 0 ∧ V.valuation (a i) ^ n.factorial = V.valuation (q : Ω) ^ e)
    ⟨-e0, by
      rintro z ⟨i, -, hz⟩
      have h1 : V.valuation (c * a i) ≤ 1 := V.valuation_le_one ⟨_, hca i⟩
      have h2 : V.valuation (c * a i) ^ n.factorial ≤ 1 := pow_le_one' h1 _
      rw [map_mul, mul_pow, he0, hz, ← zpow_add₀ h0, ← zpow_zero (V.valuation (q : Ω)),
        zpow_le_zpow_iff_right_of_lt_one₀ hpos hV] at h2
      omega⟩
    (by
      obtain ⟨i, hi⟩ := hex
      obtain ⟨e, he⟩ := hall i hi
      exact ⟨e, i, hi, he⟩)
  refine ⟨i, hi, fun i' => ?_⟩
  by_cases hi' : a i' = 0
  · rw [hi', map_zero]
    exact zero_le'
  obtain ⟨e', he'⟩ := hall i' hi'
  have h1 : V.valuation (a i') ^ n.factorial ≤ V.valuation (a i) ^ n.factorial := by
    rw [he, he', zpow_le_zpow_iff_right_of_lt_one₀ hpos hV]
    exact hmin e' ⟨i', hi', he'⟩
  by_contra hcon
  exact absurd h1 (not_le.2 (pow_lt_pow_left₀ (not_le.1 hcon) zero_le' n.factorial_ne_zero))

end GlobalTheory.ValMax
