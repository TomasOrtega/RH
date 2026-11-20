import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SingleMemOfSupportSubset
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.GradedLat

section Val

variable {L : Type} [Field L] (v : AddValuation L (WithTop ℚ))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `v.map_le_add ih (by simp)`.
-/
theorem val_nat_nonneg (n : ℕ) : 0 ≤ v (n : L) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih (by simp)

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `n.eq_nat_or_neg`. Simplify using `using val_nat_nonneg v m`. Simplify using `using val_nat_nonneg v m`.
-/
theorem val_int_nonneg (n : ℤ) : 0 ≤ v (n : L) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using val_nat_nonneg v m
  · simpa using val_nat_nonneg v m

/- English proof (translation)
Rewrite using `[v.map_mul]`. Conclude with `add_le_add ha hb`.
-/
theorem val_mul_ge {a b : L} {r t : WithTop ℚ} (ha : r ≤ v a) (hb : t ≤ v b) : r + t ≤ v (a * b) := by
  rw [v.map_mul]; exact add_le_add ha hb

/- English proof (translation)
Simplify using `using val_mul_ge v ha hb`.
-/
theorem val_mul_ge_left {a b : L} {r : WithTop ℚ} (ha : r ≤ v a) (hb : 0 ≤ v b) : r ≤ v (a * b) := by
  simpa using val_mul_ge v ha hb

/- English proof (translation)
Simplify using `using val_mul_ge v ha hb`.
-/
theorem val_mul_ge_right {a b : L} {r : WithTop ℚ} (ha : 0 ≤ v a) (hb : r ≤ v b) : r ≤ v (a * b) := by
  simpa using val_mul_ge v ha hb

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `succ n ih`. Take `⟨z, hz0, hz⟩` from `ih`. Use `⟨z + (n.choose 2 : ℕ) + y * z, v.map_le_add (v.map_le_add hz0 (val_nat_nonneg v _)) (val_mul_ge_left v hy hz0), ?_⟩` and prove the remaining obligations.

Establish `h : (1 + y) ^ n = 1 + y * ((n : L) + (n.choose 2 : ℕ) * y + y * y * z)`. Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (n + 1).choose 2 = n + n.choose 2`. Rewrite using `[Nat.choose_succ_succ' n 1, Nat.choose_one_right]`.

Rewrite using `[pow_succ, h, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expand (y : L) (hy : 0 ≤ v y) (n : ℕ) :
    ∃ z : L, 0 ≤ v z ∧ (1 + y) ^ n - 1 = y * ((n : L) + (n.choose 2 : ℕ) * y + y * y * z) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz0, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z,
      v.map_le_add (v.map_le_add hz0 (val_nat_nonneg v _)) (val_mul_ge_left v hy hz0), ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : L) + (n.choose 2 : ℕ) * y + y * y * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring

/- English proof (translation)
Introduce `hun`. Establish `hfin : IsOfFinOrder u` using `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hun⟩`. Establish `hu1 : u ≠ 1`. Introduce and unpack `rfl`. Rewrite `hu` using `[sub_self, v.map_zero]`.

Conclude with `WithTop.natCast_ne_top s hu.symm`. Establish `ho : orderOf u ≠ 1` using `fun h => hu1 (orderOf_eq_one_iff.1 h)`. Take `⟨p, hp, m, hm⟩` from `Nat.exists_prime_and_dvd ho`. Establish `hpos : 0 < orderOf u` using `hfin.orderOf_pos`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)`.

Establish `hx1 : u ^ m ≠ 1` using `pow_ne_one_of_lt_orderOf hm0.ne' (by`. Rewrite using `[hm]`. Conclude with `lt_mul_of_one_lt_left hm0 hp.one_lt)`. Establish `hxp : (u ^ m) ^ p = 1` using `by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]`. Establish `s1 : (1 : WithTop ℚ) ≤ (s : WithTop ℚ)` using `by exact_mod_cast hs`.

Establish `s0 : (0 : WithTop ℚ) ≤ (s : WithTop ℚ)` using `le_trans zero_le_one s1`. Establish `hy : (s : WithTop ℚ) ≤ v (u ^ m - 1)`. Take `⟨z, hz0, hz⟩` from `expand v (u - 1) (hu ▸ s0) m`. Rewrite `hz` using `[add_sub_cancel]`. Rewrite using `[hz]`.

Establish `h0 : 0 ≤ v (u - 1)` using `hu ▸ s0`. Conclude with `val_mul_ge_left v hu.ge (v.map_le_add (v.map_le_add (val_nat_nonneg v _) (val_mul_ge_left v (val_nat_nonneg v _) h0)) (val_mul_ge_left v (val_mul_ge_left v h0 h0) hz0))`. Use `set y := u ^ m - 1 with hydef`. Establish `hy0 : y ≠ 0` using `sub_ne_zero.2 hx1`. Take `⟨z, hz0, hz⟩` from `expand v y (s0.trans hy) p`.

Establish `: 1 + y = u ^ m` using `by rw [hydef]; ring`. Rewrite `hz` using `[this, hxp, sub_self]`. Establish `hz' : (p : L) = -((p.choose 2 : ℕ) * y + y * y * z)`. Use `(mul_eq_zero.1 hz.symm).resolve_left hy0` as an intermediate fact. Take the linear combination `this`.

Establish `y1 : (1 : WithTop ℚ) ≤ v y` using `s1.trans hy`. Establish `hB : (1 + 1 : WithTop ℚ) ≤ v (y * y * z)` using `val_mul_ge_left v (val_mul_ge v y1 y1) hz0`. Establish `lt12 : (1 : WithTop ℚ) < 1 + 1`. Conclude with `(by norm_num : (1 : ℚ) < 1 + 1)` after adjusting the coercions. Distinguish the cases in `hpl : p = l`.

Substitute `hpl` using the available equality. Establish `hA : (1 + 1 : WithTop ℚ) ≤ v (((p.choose 2 : ℕ) : L) * y)`. Distinguish the cases in `h : p = 2`. Establish `: (1 + 1 : WithTop ℚ) ≤ (s : WithTop ℚ)` using `by exact_mod_cast h2 h`. Conclude with `val_mul_ge_right v (val_nat_nonneg v _) (this.trans hy)`.

Take `⟨c, hc⟩` from `hp.dvd_choose_self (k := 2) (by norm_num) (lt_of_le_of_ne hp.two_le (Ne.symm h))`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `val_mul_ge v (val_mul_ge_left v hv.ge (val_nat_nonneg v _)) y1`. Use `v.map_le_add hA hB` as an intermediate fact. Rewrite `this` using `[← v.map_neg, ← hz', hv]`.

Conclude with `absurd this (not_le.2 lt12)`. Establish `hA : (1 : WithTop ℚ) ≤ v (((p.choose 2 : ℕ) : L) * y)` using `val_mul_ge_right v (val_nat_nonneg v _) y1`. Establish `hP` using `v.map_le_add hA (lt12.le.trans hB)`. Rewrite `hP` using `[← v.map_neg, ← hz']`. Establish `hcop : IsCoprime (p : ℤ) (l : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)`.

Take `⟨a, b, hab⟩` from `hcop`. Establish `hab' : (a : L) * p + (b : L) * l = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → L) hab`. Use `v.map_le_add (val_mul_ge_right v (val_int_nonneg v a) hP) (val_mul_ge_right v (val_int_nonneg v b) hv.ge)` as an intermediate fact. Rewrite `this` using `[hab', v.map_one]`. Conclude with `absurd this (not_le.2 zero_lt_one)`.
-/
theorem pow_ne_one {l : ℕ} (hl : l.Prime) (hv : v (l : L) = 1) {s : ℕ} (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s)
    {u : L} (hu : v (u - 1) = (s : WithTop ℚ)) {n : ℕ} (hn : 0 < n) : u ^ n ≠ 1 := by
  intro hun
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hun⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [sub_self, v.map_zero] at hu
    exact WithTop.natCast_ne_top s hu.symm
  have ho : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd ho
  have hpos : 0 < orderOf u := hfin.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hx1 : u ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by
    rw [hm]; exact lt_mul_of_one_lt_left hm0 hp.one_lt)
  have hxp : (u ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have s1 : (1 : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast hs
  have s0 : (0 : WithTop ℚ) ≤ (s : WithTop ℚ) := le_trans zero_le_one s1
  have hy : (s : WithTop ℚ) ≤ v (u ^ m - 1) := by
    obtain ⟨z, hz0, hz⟩ := expand v (u - 1) (hu ▸ s0) m
    rw [add_sub_cancel] at hz
    rw [hz]
    have h0 : 0 ≤ v (u - 1) := hu ▸ s0
    exact val_mul_ge_left v hu.ge (v.map_le_add (v.map_le_add (val_nat_nonneg v _)
      (val_mul_ge_left v (val_nat_nonneg v _) h0)) (val_mul_ge_left v (val_mul_ge_left v h0 h0) hz0))
  set y := u ^ m - 1 with hydef
  have hy0 : y ≠ 0 := sub_ne_zero.2 hx1
  obtain ⟨z, hz0, hz⟩ := expand v y (s0.trans hy) p
  have : 1 + y = u ^ m := by rw [hydef]; ring
  rw [this, hxp, sub_self] at hz
  have hz' : (p : L) = -((p.choose 2 : ℕ) * y + y * y * z) := by
    have := (mul_eq_zero.1 hz.symm).resolve_left hy0
    linear_combination this
  have y1 : (1 : WithTop ℚ) ≤ v y := s1.trans hy
  have hB : (1 + 1 : WithTop ℚ) ≤ v (y * y * z) := val_mul_ge_left v (val_mul_ge v y1 y1) hz0
  have lt12 : (1 : WithTop ℚ) < 1 + 1 := by
    exact_mod_cast (by norm_num : (1 : ℚ) < 1 + 1)
  by_cases hpl : p = l
  · subst hpl
    have hA : (1 + 1 : WithTop ℚ) ≤ v (((p.choose 2 : ℕ) : L) * y) := by
      by_cases h : p = 2
      · have : (1 + 1 : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast h2 h
        exact val_mul_ge_right v (val_nat_nonneg v _) (this.trans hy)
      · obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num)
          (lt_of_le_of_ne hp.two_le (Ne.symm h))
        rw [hc, Nat.cast_mul]
        exact val_mul_ge v (val_mul_ge_left v hv.ge (val_nat_nonneg v _)) y1
    have := v.map_le_add hA hB
    rw [← v.map_neg, ← hz', hv] at this
    exact absurd this (not_le.2 lt12)
  · have hA : (1 : WithTop ℚ) ≤ v (((p.choose 2 : ℕ) : L) * y) :=
      val_mul_ge_right v (val_nat_nonneg v _) y1
    have hP := v.map_le_add hA (lt12.le.trans hB)
    rw [← v.map_neg, ← hz'] at hP
    have hcop : IsCoprime (p : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hl).2 hpl)
    obtain ⟨a, b, hab⟩ := hcop
    have hab' : (a : L) * p + (b : L) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → L) hab
    have := v.map_le_add (val_mul_ge_right v (val_int_nonneg v a) hP)
      (val_mul_ge_right v (val_int_nonneg v b) hv.ge)
    rw [hab', v.map_one] at this
    exact absurd this (not_le.2 zero_lt_one)

/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `hu` using `[zero_sub, v.map_neg, v.map_one]`. Establish `: (0 : ℕ) = s` using `by exact_mod_cast hu`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_zero_of_val {s : ℕ} (hs : 1 ≤ s) {u : L} (hu : v (u - 1) = (s : WithTop ℚ)) : u ≠ 0 := by
  rintro rfl
  rw [zero_sub, v.map_neg, v.map_one] at hu
  have : (0 : ℕ) = s := by exact_mod_cast hu
  omega

/- English proof (translation)
Take `⟨m, rfl | rfl⟩` from `k.eq_nat_or_neg`. Rewrite using `[zpow_natCast]; exact pow_ne_one v hl hv hs h2 hu (by omega)`. Rewrite using `[zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact pow_ne_one v hl hv hs h2 hu (by omega)`.
-/
theorem zpow_ne_one {l : ℕ} (hl : l.Prime) (hv : v (l : L) = 1) {s : ℕ} (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s)
    {u : L} (hu : v (u - 1) = (s : WithTop ℚ)) (k : ℤ) (hk : k ≠ 0) : u ^ k ≠ 1 := by
  obtain ⟨m, rfl | rfl⟩ := k.eq_nat_or_neg
  · rw [zpow_natCast]; exact pow_ne_one v hl hv hs h2 hu (by omega)
  · rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]; exact pow_ne_one v hl hv hs h2 hu (by omega)

end Val

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

/- English proof (translation)
Take `⟨m, hm⟩` from `hF`. Establish `hval : ∀ (x : ℤ → M) (a : ℤ) k, (∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M)) k = if k ∈ Finset.Ico a m then x k else 0`. Introduce `x a k`. Simplify using `only [Finset.sum_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_ite_eq]`.

Establish `tail : ∀ (x : ℤ → M) (a : ℤ), (∀ k, x k ∈ D) → (∀ k < a, x k = 0) → x - ∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M) ∈ Λ`. Introduce `x a hD hx`. Apply `hm` to reduce the goal to its premises. Introduce `k`. Rewrite using `[Pi.sub_apply, hval]`.

Use `split_ifs`. Simplify using the standard rewrite rules. Simplify using `using hD k`. Introduce `k hk`. Rewrite using `[Pi.sub_apply, hval]`.

Distinguish the cases in `h : k < a`. Simplify using `[hx k h]`. Establish `: k ∈ Finset.Ico a m` using `Finset.mem_Ico.mpr ⟨not_lt.mp h, hk⟩`. Simplify using `[this]`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨hD, a, ha⟩` from `hc x hx`. Use `⟨⟨a, ha⟩, fun k => ?_⟩` and prove the remaining obligations. Establish `h1 : ∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M) ∈ Λ`.

Use `Λ.sub_mem hx (tail x a hD ha)` as an intermediate fact. Simplify using `using this`. Establish `h2` using `GlobalTheory.Per.single_mem_of_support_subset u Λ hu hr hγ (Finset.Ico a m) _ h1 (fun k hk => by rw [hval, if_neg hk]) k`. Distinguish the cases in `hk : k ∈ Finset.Ico a (m : ℤ)`. Rewrite `h2` using `[hval, if_pos hk]`. Then use the resulting hypothesis.

Distinguish the cases in `hk' : k < a`. Rewrite using `[ha k hk']`. Simplify using the standard rewrite rules. Apply `hm` to reduce the goal to its premises. Introduce `j`.

Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality. Simplify using `using hD j`. Simplify using `[Pi.single_eq_of_ne hjk]`. Introduce `i hi`.

Establish `: i ≠ k`. Introduce and unpack `rfl`. Conclude with `hk (Finset.mem_Ico.mpr ⟨not_lt.mp hk', hi⟩)`. Simplify using `[this]`. Introduce and unpack `⟨⟨a, ha⟩, h2⟩`.

Establish `hD : ∀ k, x k ∈ D` using `fun k => by simpa using (hc _ (h2 k)).1 k`. Use `Λ.add_mem (tail x a hD ha) (Λ.sum_mem (t := Finset.Ico a m) fun i _ => h2 i)` as an intermediate fact. Simplify using `using this`.
-/
theorem graded_of_full (u : L) (D : Submodule L M) (Λ : Submodule L (ℤ → M)) (hu : u ≠ 0)
    (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1) (hF : Full D Λ)
    (hc : ∀ f ∈ Λ, (∀ k, f k ∈ D) ∧ ∃ m : ℤ, ∀ k < m, f k = 0)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) : Graded Λ := by
  classical
  obtain ⟨m, hm⟩ := hF
  have hval : ∀ (x : ℤ → M) (a : ℤ) k, (∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M)) k
      = if k ∈ Finset.Ico a m then x k else 0 := by
    intro x a k
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
  have tail : ∀ (x : ℤ → M) (a : ℤ), (∀ k, x k ∈ D) → (∀ k < a, x k = 0) →
      x - ∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M) ∈ Λ := by
    intro x a hD hx
    apply hm
    · intro k
      rw [Pi.sub_apply, hval]
      split_ifs
      · simp
      · simpa using hD k
    · intro k hk
      rw [Pi.sub_apply, hval]
      by_cases h : k < a
      · simp [hx k h]
      · have : k ∈ Finset.Ico a m := Finset.mem_Ico.mpr ⟨not_lt.mp h, hk⟩
        simp [this]
  intro x
  constructor
  · intro hx
    obtain ⟨hD, a, ha⟩ := hc x hx
    refine ⟨⟨a, ha⟩, fun k => ?_⟩
    have h1 : ∑ i ∈ Finset.Ico a m, (Pi.single i (x i) : ℤ → M) ∈ Λ := by
      have := Λ.sub_mem hx (tail x a hD ha)
      simpa using this
    have h2 := GlobalTheory.Per.single_mem_of_support_subset u Λ hu hr hγ (Finset.Ico a m) _ h1
      (fun k hk => by rw [hval, if_neg hk]) k
    by_cases hk : k ∈ Finset.Ico a (m : ℤ)
    · rwa [hval, if_pos hk] at h2
    · by_cases hk' : k < a
      · rw [ha k hk']; simp
      · apply hm
        · intro j
          by_cases hjk : j = k
          · subst hjk; simpa using hD j
          · simp [Pi.single_eq_of_ne hjk]
        · intro i hi
          have : i ≠ k := by
            rintro rfl
            exact hk (Finset.mem_Ico.mpr ⟨not_lt.mp hk', hi⟩)
          simp [this]
  · rintro ⟨⟨a, ha⟩, h2⟩
    have hD : ∀ k, x k ∈ D := fun k => by simpa using (hc _ (h2 k)).1 k
    have := Λ.add_mem (tail x a hD ha) (Λ.sum_mem (t := Finset.Ico a m) fun i _ => h2 i)
    simpa using this

/- English proof (translation)
Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨p, x, rfl⟩` from `hf`. Take `⟨y, hy⟩` from `he x`.

Take `⟨m, hm⟩` from `hs x`. Use `Submodule.subset_span ⟨PowerSeries.rescale u p, y, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Unfold `conv`. Rewrite using `[smul_finsum' _ (Model.conv_finite p hm k)]`.

Use `finsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[hy, PowerSeries.coeff_rescale, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[zpow_sub₀ hu, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Consider the case `zero`. Use `(latSpan (LL := L) e).zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Consider the case `add f g _ _ hf hg`.

Use `(latSpan (LL := L) e).add_mem hf hg` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Consider the case `smul c f _ hf`.

Use `(latSpan (LL := L) e).smul_mem c hf` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[smul_comm c]`.
-/
theorem latSpan_stable {ι : Type} (u : L) (hu : u ≠ 0) (e : ι → ℤ → M)
    (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0) (he : ∀ x, ∃ y, ∀ k, e y k = u ^ k • e x k) :
    ∀ f ∈ latSpan (LL := L) e, (fun k => u ^ k • f k) ∈ latSpan (LL := L) e := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨p, x, rfl⟩ := hf
    obtain ⟨y, hy⟩ := he x
    obtain ⟨m, hm⟩ := hs x
    refine Submodule.subset_span ⟨PowerSeries.rescale u p, y, ?_⟩
    funext k
    unfold conv
    rw [smul_finsum' _ (Model.conv_finite p hm k)]
    refine finsum_congr fun j => ?_
    rw [hy, PowerSeries.coeff_rescale, smul_smul, smul_smul]
    congr 1
    rw [zpow_sub₀ hu, zpow_natCast]
    field_simp
  | zero =>
    convert (latSpan (LL := L) e).zero_mem using 1
    funext k; simp
  | add f g _ _ hf hg =>
    have := (latSpan (LL := L) e).add_mem hf hg
    convert this using 1
    funext k; simp
  | smul c f _ hf =>
    have := (latSpan (LL := L) e).smul_mem c hf
    convert this using 1
    funext k; simp [smul_comm c]

end Series

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hg` using `(H.W K s LL h).gam_gen`. Rewrite `hg` using `[H.W_s]`. Take `⟨j, hj, hord⟩` from `(Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)`. Establish `hjs : (j : WithTop ℚ) ≤ (s : WithTop ℚ)` using `by exact_mod_cast hj`. Conclude with `(C.C K s LL h).tie.levB_Γ T hT (H.W K s LL h).gam i ζ ζ j 1 (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ) (by rw [Nat.cast_one]; exact hjs.trans hg.ge) (pow_one ζ).symm x ((H.W K s LL h).N_Γ T (H.W K s LL h).gam x x.2) k`.
-/
theorem ex_gam {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1)
    (hζ : ζ ^ (l ^ s) = 1) (x : ↥((H.W K s LL h).N T)) (k : ℤ) :
    ex C h T i ζ ⟨_, (H.W K s LL h).N_Γ T (H.W K s LL h).gam x x.2⟩ k =
      (algebraMap ↥(OL LL) ↥LL.1 ((H.W K s LL h).χΓ (H.W K s LL h).gam : ↥(OL LL))) ^ k •
        ex C h T i ζ x k := by
  have hg := (H.W K s LL h).gam_gen
  rw [H.W_s] at hg
  obtain ⟨j, hj, hord⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one hζ)
  have hjs : (j : WithTop ℚ) ≤ (s : WithTop ℚ) := by exact_mod_cast hj
  exact (C.C K s LL h).tie.levB_Γ T hT (H.W K s LL h).gam i ζ ζ j 1
    (by rw [P.PD_p, ← hord]; exact IsPrimitiveRoot.orderOf ζ)
    (by rw [Nat.cast_one]; exact hjs.trans hg.ge) (pow_one ζ).symm x
    ((H.W K s LL h).N_Γ T (H.W K s LL h).gam x x.2) k

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hg` using `(H.W K s LL h).gam_gen`. Establish `hv` using `(H.W K s LL h).v_l`. Establish `h1` using `(H.W K s LL h).s_pos`. Establish `h2` using `(H.W K s LL h).s_two`. Rewrite `hv`, `h2` using `[P.PD_p]`.

Establish `hu` using `ne_zero_of_val _ h1 hg`. Conclude with `graded_of_full _ _ _ hu (zpow_ne_one _ Fact.out hv h1 h2 hg) hF (Model.Lat_coeff C h T i ζ) (latSpan_stable _ hu _ (fun x => (C.C K s LL h).tie.levB_supp T i ζ x) (fun x => ⟨_, ex_gam C h T hT i ζ hζ x⟩))`.
-/
theorem graded_Lat {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {F : LocFon l P AI H} (C : LocCmpT l P AI H F) {K : FinExt l} {s : ℕ} {LL : FinExt l}
    (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (i : Let K) (ζ : ↥LL.1)
    (hζ : ζ ^ (l ^ s) = 1) (hF : Full (Di H h T i) (Lat C h T i ζ)) : Graded (Lat C h T i ζ) := by
  have hg := (H.W K s LL h).gam_gen
  have hv := (H.W K s LL h).v_l
  have h1 := (H.W K s LL h).s_pos
  have h2 := (H.W K s LL h).s_two
  rw [P.PD_p] at hv h2
  have hu := ne_zero_of_val _ h1 hg
  exact graded_of_full _ _ _ hu (zpow_ne_one _ Fact.out hv h1 h2 hg) hF
    (Model.Lat_coeff C h T i ζ)
    (latSpan_stable _ hu _ (fun x => (C.C K s LL h).tie.levB_supp T i ζ x)
      (fun x => ⟨_, ex_gam C h T hT i ζ hζ x⟩))

/- English proof (translation)
Introduce `D HW F Cm l _ K s LL h W E C T hT i ζ hζ hF`. Conclude with `graded_Lat C h T hT i ζ hζ hF`.
-/
theorem graded_of_level_le : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ s) = 1 → Full (Di (HW l) h T i) (Lat C h T i ζ) → Graded (Lat C h T i ζ) := by
  intro D HW F Cm l _ K s LL h W E C T hT i ζ hζ hF
  exact graded_Lat C h T hT i ζ hζ hF

end GlobalTheory.NL.GradedLat
