import Mathlib
import GroundTheory.LocalFields.PadicExp

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

variable (K) in

noncomputable def principalFiltration (k : ℕ) : AddSubgroup (Additive (unitFiltrationUnits K 1)) :=
  Subgroup.toAddSubgroup ((unitFiltrationUnits K (k + 1)).comap (unitFiltrationUnits K 1).subtype)

/- English proof (translation)
Use `mem_unitFiltrationUnits_iff_valBall (K := K) (n := k + 1) (by omega) (x := ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ))` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
theorem mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)} :
    u ∈ principalFiltration K k ↔
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) ∈ valBall K (k + 1) := by
  have := mem_unitFiltrationUnits_iff_valBall (K := K) (n := k + 1) (by omega)
    (x := ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ))
  push_cast at this
  exact this

/- English proof (translation)
Introduce `j k hjk u hu`. Rewrite `hu`, the goal using `[mem_principalFiltration]`. Conclude with `valBall_antitone (by omega) hu`.
-/
theorem principalFiltration_antitone : Antitone (principalFiltration K) := by
  intro j k hjk u hu
  rw [mem_principalFiltration] at hu ⊢
  exact valBall_antitone (by omega) hu

/- English proof (translation)
Use extensionality with `u`. Simplify using `only [AddSubgroup.mem_top, iff_true, mem_principalFiltration]`. Simplify using `using sub_one_mem_valBall_one (Additive.toMul u)`.
-/
theorem principalFiltration_zero : principalFiltration K 0 = ⊤ := by
  ext u
  simp only [AddSubgroup.mem_top, iff_true, mem_principalFiltration]
  simpa using sub_one_mem_valBall_one (Additive.toMul u)

/- English proof (translation)
Establish `h : normalizedValuation K (y - 1) < 1`. Use `lt_of_le_of_lt hy ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Use `Valuation.map_one_add_of_lt (normalizedValuation K) h` as an intermediate fact.

Simplify using `using this`.
-/
theorem normalizedValuation_eq_one_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) :
    normalizedValuation K y = 1 := by
  have h : normalizedValuation K (y - 1) < 1 := by
    refine lt_of_le_of_lt hy ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have := Valuation.map_one_add_of_lt (normalizedValuation K) h
  simpa using this

/- English proof (translation)
Rewrite using `[mem_valBall, normalizedValuation_eq_one_of_sub_one_mem hy]`. Simplify using the standard rewrite rules.
-/
theorem mem_valBall_zero_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) : y ∈ valBall K 0 := by
  rw [mem_valBall, normalizedValuation_eq_one_of_sub_one_mem hy]; simp

/- English proof (translation)
Use `set y : K := (((Additive.toMul w : unitFiltrationUnits K 1) : Kˣ) : K) - 1`. Establish `hy : y = 0`. Assume the negation of the conclusion as `hy0`. Establish `hk` using `mem_principalFiltration.mp (h (ord y).toNat)`. Rewrite `hk` using `[mem_valBall, normalizedValuation_eq_exp_ord hy0, WithZero.exp_le_exp]`.

Use `Int.self_le_toNat (ord y)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply `Additive.toMul.injective` to reduce the goal to its premises. Use `ext`. Simplify `hy` using `[y, sub_eq_zero]`.
-/
theorem eq_zero_of_forall_mem_principalFiltration {w : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k, w ∈ principalFiltration K k) : w = 0 := by
  set y : K := (((Additive.toMul w : unitFiltrationUnits K 1) : Kˣ) : K) - 1
  have hy : y = 0 := by
    by_contra hy0
    have hk := mem_principalFiltration.mp (h (ord y).toNat)
    rw [mem_valBall, normalizedValuation_eq_exp_ord hy0, WithZero.exp_le_exp] at hk
    have := Int.self_le_toNat (ord y)
    omega
  apply Additive.toMul.injective
  ext
  simpa [y, sub_eq_zero] using hy

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

omit hp in
/- English proof (translation)
Establish `h : ((p : 𝒪[K]) : 𝒪[K]) ∈ 𝓂[K] ^ 1`. Rewrite using `[pow_one, ← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]`. Use `mem_maximalIdeal_pow_iff_valBall.mp h` as an intermediate fact. Simplify using `using this`.
-/
theorem natCast_prime_mem_valBall_one : (p : K) ∈ valBall K 1 := by
  have h : ((p : 𝒪[K]) : 𝒪[K]) ∈ 𝓂[K] ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have := mem_maximalIdeal_pow_iff_valBall.mp h
  simpa using this

/- English proof (translation)
Use `set x := y - 1`. Establish `hyx : y = x + 1` using `by ring`. Rewrite using `[hyx, add_pow, Finset.sum_range_succ']`. Simplify using `only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]`. Use `AddSubgroup.sum_mem _ fun i hi ↦ ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_range]`. Break down `Nat.lt_or_ge (i + 1) p with hlt | hge` into its components or cases. Take `⟨c, hc⟩` from `hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt`. Rewrite using `[hc, Nat.cast_mul]`. Establish `h1 : (p : K) * (c : K) ∈ valBall K (1 + 0)` using `mul_mem_valBall (natCast_prime_mem_valBall_one p) (by simpa using intCast_mem_valBall_zero (K := K) (c : ℤ))`.

Establish `h2` using `mul_mem_valBall (pow_mem_valBall hy (i + 1)) h1`. Use `valBall_antitone ?_ h2` and prove the remaining obligations. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hi' : i + 1 = p` using `by omega`.

Rewrite using `[hi', Nat.choose_self, Nat.cast_one, mul_one]`. Use `valBall_antitone ?_ (pow_mem_valBall hy p)` and prove the remaining obligations. Establish `: (2 : ℤ) ≤ p` using `by exact_mod_cast hp.out.two_le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem pow_prime_sub_one_mem {k : ℤ} (hk : 1 ≤ k) {y : K} (hy : y - 1 ∈ valBall K k) :
    y ^ p - 1 ∈ valBall K (k + 1) := by
  set x := y - 1
  have hyx : y = x + 1 := by ring
  rw [hyx, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases Nat.lt_or_ge (i + 1) p with hlt | hge
  · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt
    rw [hc, Nat.cast_mul]
    have h1 : (p : K) * (c : K) ∈ valBall K (1 + 0) :=
      mul_mem_valBall (natCast_prime_mem_valBall_one p)
        (by simpa using intCast_mem_valBall_zero (K := K) (c : ℤ))
    have h2 := mul_mem_valBall (pow_mem_valBall hy (i + 1)) h1
    refine valBall_antitone ?_ h2
    push_cast; nlinarith
  · have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, mul_one]
    refine valBall_antitone ?_ (pow_mem_valBall hy p)
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    nlinarith

/- English proof (translation)
Rewrite `hu`, the goal using `[mem_principalFiltration]`. Use `pow_prime_sub_one_mem p (by omega) hu` as an intermediate fact. Simplify using `using this`.
-/
theorem nsmul_prime_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : p • u ∈ principalFiltration K (k + 1) := by
  rw [mem_principalFiltration] at hu ⊢
  have := pow_prime_sub_one_mem p (by omega) hu
  simpa using this

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hu`. Consider the case `succ j ih`. Rewrite using `[show p ^ (j + 1) • u = p • (p ^ j • u) by rw [smul_smul, ← pow_succ'], ← add_assoc]`. Conclude with `nsmul_prime_mem_principalFiltration p ih`.
-/
theorem nsmul_prime_pow_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) (j : ℕ) : p ^ j • u ∈ principalFiltration K (k + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [show p ^ (j + 1) • u = p • (p ^ j • u) by rw [smul_smul, ← pow_succ'], ← add_assoc]
    exact nsmul_prime_mem_principalFiltration p ih

/- English proof (translation)
Take `⟨d, rfl⟩` from `hc`. Rewrite using `[mul_comm, mul_zsmul]`. Use `zsmul_mem ?_ d` and prove the remaining obligations. Use `nsmul_prime_pow_mem_principalFiltration p (by rw [principalFiltration_zero]; trivial : u ∈ principalFiltration K 0) k` as an intermediate fact. Rewrite `this` using `[zero_add]`.

Conclude with `this` after adjusting the coercions.
-/
theorem zsmul_mem_principalFiltration_of_dvd {k : ℕ} {c : ℤ} (hc : (p ^ k : ℤ) ∣ c)
    (u : Additive (unitFiltrationUnits K 1)) : c • u ∈ principalFiltration K k := by
  obtain ⟨d, rfl⟩ := hc
  rw [mul_comm, mul_zsmul]
  refine zsmul_mem ?_ d
  have := nsmul_prime_pow_mem_principalFiltration p
    (by rw [principalFiltration_zero]; trivial : u ∈ principalFiltration K 0) k
  rw [zero_add] at this
  exact_mod_cast this

end Filtration

section Complete

/- English proof (translation)
Use `set σ : ℕ → K := fun k ↦ (((Additive.toMul (s k) : unitFiltrationUnits K 1) : Kˣ) : K)`. Establish `hσ1 : ∀ k, σ k - 1 ∈ valBall K 1` using `fun k ↦ sub_one_mem_valBall_one (Additive.toMul (s k))`. Establish `hσ0 : ∀ k, σ k ≠ 0` using `fun k ↦ Units.ne_zero _`. Establish `hquot : ∀ k : ℕ, σ (k + 1) / σ k - 1 ∈ valBall K (k + 1)`. Introduce `k`.

Use `mem_principalFiltration.mp (hs k)` as an intermediate fact. Simplify `this` using `[σ, toMul_sub, div_eq_mul_inv]`. Use `set f : ℕ → K := fun j ↦ σ (j + 1) - σ j`. Establish `hf : ∀ j : ℕ, f j ∈ valBall K (j + 1)`. Introduce `j`.

Establish `h : f j = σ j * (σ (j + 1) / σ j - 1)`. Simplify using `only [f]`. Clear denominators, using `[hσ0 j]` for the nonvanishing conditions. Rewrite using `[h]`. Simplify using `using mul_mem_valBall (mem_valBall_zero_of_sub_one_mem (hσ1 j)) (hquot j)`.

Establish `hsum : Summable f`. Use `summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)` and prove the remaining obligations. Rewrite using `[eventually_atTop]`. Conclude with `⟨N.toNat, fun j hj ↦ valBall_antitone (by have := Int.self_le_toNat N; omega) (hf j)⟩`. Use `set L := σ 0 + ∑' j, f j`.

Establish `hL : ∀ k : ℕ, L - σ k = ∑' j, f (j + k)`. Introduce `k`. Establish `h1` using `hsum.sum_add_tsum_nat_add k`. Establish `h2 : ∑ i ∈ Finset.range k, f i = σ k - σ 0` using `Finset.sum_range_sub σ k`. Simplify using `only [L]`.

Rewrite using `[← h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLk : ∀ k : ℕ, L - σ k ∈ valBall K (k + 1)`. Introduce `k`. Rewrite using `[hL k]`.

Conclude with `tsum_mem_valBall fun j ↦ valBall_antitone (by omega) (hf (j + k))`. Establish `hL1 : L - 1 ∈ valBall K 1`. Use `add_mem (hLk 0) (hσ1 0)` as an intermediate fact. Simplify using `using this`. Establish `hL0 : L ≠ 0`.

Introduce `h`. Use `normalizedValuation_eq_one_of_sub_one_mem hL1` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Use `⟨Additive.ofMul ⟨Units.mk0 L hL0, (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩, fun k ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_principalFiltration]`. Establish `heq : (((Additive.toMul (Additive.ofMul ⟨Units.mk0 L hL0, (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩ - s k) : unitFiltrationUnits K 1) : Kˣ) : K) - 1 = (L - σ k) * (σ k)⁻¹`. Simplify using `only [toMul_sub, toMul_ofMul]`. Simplify using `[σ, div_eq_mul_inv]`. Clear denominators, using `[hσ0 k]` for the nonvanishing conditions.

Rewrite using `[heq]`. Establish `hinv : (σ k)⁻¹ ∈ valBall K 0`. Rewrite using `[mem_valBall, map_inv₀, normalizedValuation_eq_one_of_sub_one_mem (hσ1 k)]`. Simplify using the standard rewrite rules. Simplify using `using mul_mem_valBall (hLk k) hinv`.
-/
theorem exists_forall_sub_mem_principalFiltration {s : ℕ → Additive (unitFiltrationUnits K 1)}
    (hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k) :
    ∃ l, ∀ k, l - s k ∈ principalFiltration K k := by
  set σ : ℕ → K := fun k ↦ (((Additive.toMul (s k) : unitFiltrationUnits K 1) : Kˣ) : K)
  have hσ1 : ∀ k, σ k - 1 ∈ valBall K 1 := fun k ↦ sub_one_mem_valBall_one (Additive.toMul (s k))
  have hσ0 : ∀ k, σ k ≠ 0 := fun k ↦ Units.ne_zero _
  have hquot : ∀ k : ℕ, σ (k + 1) / σ k - 1 ∈ valBall K (k + 1) := by
    intro k
    have := mem_principalFiltration.mp (hs k)
    simpa [σ, toMul_sub, div_eq_mul_inv] using this
  set f : ℕ → K := fun j ↦ σ (j + 1) - σ j
  have hf : ∀ j : ℕ, f j ∈ valBall K (j + 1) := by
    intro j
    have h : f j = σ j * (σ (j + 1) / σ j - 1) := by
      simp only [f]; field_simp [hσ0 j]
    rw [h]
    simpa using mul_mem_valBall (mem_valBall_zero_of_sub_one_mem (hσ1 j)) (hquot j)
  have hsum : Summable f := by
    refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
    rw [eventually_atTop]
    exact ⟨N.toNat, fun j hj ↦ valBall_antitone (by have := Int.self_le_toNat N; omega) (hf j)⟩
  set L := σ 0 + ∑' j, f j
  have hL : ∀ k : ℕ, L - σ k = ∑' j, f (j + k) := by
    intro k
    have h1 := hsum.sum_add_tsum_nat_add k
    have h2 : ∑ i ∈ Finset.range k, f i = σ k - σ 0 := Finset.sum_range_sub σ k
    simp only [L]
    rw [← h1, h2]
    ring
  have hLk : ∀ k : ℕ, L - σ k ∈ valBall K (k + 1) := by
    intro k
    rw [hL k]
    exact tsum_mem_valBall fun j ↦ valBall_antitone (by omega) (hf (j + k))
  have hL1 : L - 1 ∈ valBall K 1 := by
    have := add_mem (hLk 0) (hσ1 0)
    simpa using this
  have hL0 : L ≠ 0 := by
    intro h
    have := normalizedValuation_eq_one_of_sub_one_mem hL1
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨Additive.ofMul ⟨Units.mk0 L hL0,
    (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩, fun k ↦ ?_⟩
  rw [mem_principalFiltration]
  have heq : (((Additive.toMul (Additive.ofMul ⟨Units.mk0 L hL0,
      (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩ - s k) :
        unitFiltrationUnits K 1) : Kˣ) : K) - 1 = (L - σ k) * (σ k)⁻¹ := by
    simp only [toMul_sub, toMul_ofMul]
    simp [σ, div_eq_mul_inv]
    field_simp [hσ0 k]
  rw [heq]
  have hinv : (σ k)⁻¹ ∈ valBall K 0 := by
    rw [mem_valBall, map_inv₀, normalizedValuation_eq_one_of_sub_one_mem (hσ1 k)]; simp
  simpa using mul_mem_valBall (hLk k) hinv

end Complete

section Module

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd]`.
-/
theorem padicInt_dvd_intCast_iff {k : ℕ} {c : ℤ} :
    (p : ℤ_[p]) ^ k ∣ (c : ℤ_[p]) ↔ ((p : ℤ) ^ k) ∣ c := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_int_le_pow_iff_dvd]

/- English proof (translation)
Rewrite using `[← padicInt_dvd_intCast_iff]`. Use `dvd_sub h h'` as an intermediate fact. Use `push_cast`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem intCast_dvd_sub_of_dvd_sub {k : ℕ} {a : ℤ_[p]} {c c' : ℤ} (h : (p : ℤ_[p]) ^ k ∣ a - c)
    (h' : (p : ℤ_[p]) ^ k ∣ a - c') : ((p : ℤ) ^ k) ∣ c' - c := by
  rw [← padicInt_dvd_intCast_iff]
  have := dvd_sub h h'
  push_cast
  convert this using 1
  ring

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton]`. Simplify using `using PadicInt.appr_spec k a`.
-/
theorem dvd_sub_appr (k : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ k ∣ a - ((a.appr k : ℕ) : ℤ) := by
  rw [← Ideal.mem_span_singleton]
  simpa using PadicInt.appr_spec k a

variable [CharP 𝓀[K] p]

/- English proof (translation)
Use `set s : ℕ → Additive (unitFiltrationUnits K 1) := fun k ↦ ((a.appr k : ℕ) : ℤ) • u`. Establish `hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k`. Introduce `k`. Simplify using `only [s]`. Rewrite using `[show ((a.appr (k + 1) : ℕ) : ℤ) • u - ((a.appr k : ℕ) : ℤ) • u = (((a.appr (k + 1) : ℕ) : ℤ) - ((a.appr k : ℕ) : ℤ)) • u by rw [sub_zsmul]; abel]`.

Use `zsmul_mem_principalFiltration_of_dvd p ?_ u` and prove the remaining obligations. Establish `h1` using `dvd_sub_appr p (k + 1) a`. Establish `h1' : (p : ℤ_[p]) ^ k ∣ a - ((a.appr (k + 1) : ℕ) : ℤ)` using `(pow_dvd_pow _ (Nat.le_succ k)).trans h1`. Use `intCast_dvd_sub_of_dvd_sub p (dvd_sub_appr p k a) h1'` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Take `⟨l, hl⟩` from `exists_forall_sub_mem_principalFiltration hs`. Use `⟨l, fun k c hc ↦ ?_⟩` and prove the remaining obligations. Establish `h` using `intCast_dvd_sub_of_dvd_sub p hc (dvd_sub_appr p k a)`. Establish `: l - c • u = (l - s k) + (((a.appr k : ℕ) : ℤ) - c) • u`. Simplify using `only [s, sub_zsmul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `add_mem (hl k) (zsmul_mem_principalFiltration_of_dvd p h u)`.
-/
theorem exists_padicInt_pow (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    ∃ l : Additive (unitFiltrationUnits K 1), ∀ (k : ℕ) (c : ℤ), (p : ℤ_[p]) ^ k ∣ a - c →
      l - c • u ∈ principalFiltration K k := by
  set s : ℕ → Additive (unitFiltrationUnits K 1) := fun k ↦ ((a.appr k : ℕ) : ℤ) • u
  have hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k := by
    intro k
    simp only [s]
    rw [show ((a.appr (k + 1) : ℕ) : ℤ) • u - ((a.appr k : ℕ) : ℤ) • u =
      (((a.appr (k + 1) : ℕ) : ℤ) - ((a.appr k : ℕ) : ℤ)) • u by rw [sub_zsmul]; abel]
    refine zsmul_mem_principalFiltration_of_dvd p ?_ u
    have h1 := dvd_sub_appr p (k + 1) a
    have h1' : (p : ℤ_[p]) ^ k ∣ a - ((a.appr (k + 1) : ℕ) : ℤ) :=
      (pow_dvd_pow _ (Nat.le_succ k)).trans h1
    have := intCast_dvd_sub_of_dvd_sub p (dvd_sub_appr p k a) h1'
    exact_mod_cast this
  obtain ⟨l, hl⟩ := exists_forall_sub_mem_principalFiltration hs
  refine ⟨l, fun k c hc ↦ ?_⟩
  have h := intCast_dvd_sub_of_dvd_sub p hc (dvd_sub_appr p k a)
  have : l - c • u = (l - s k) + (((a.appr k : ℕ) : ℤ) - c) • u := by
    simp only [s, sub_zsmul]; abel
  rw [this]
  exact add_mem (hl k) (zsmul_mem_principalFiltration_of_dvd p h u)

noncomputable def padicIntSMul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    Additive (unitFiltrationUnits K 1) :=
  Classical.choose (exists_padicInt_pow p a u)

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_padicInt_pow p a u) k c hc`.
-/
theorem padicIntSMul_spec (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) {k : ℕ} {c : ℤ}
    (hc : (p : ℤ_[p]) ^ k ∣ a - c) : padicIntSMul p a u - c • u ∈ principalFiltration K k :=
  Classical.choose_spec (exists_padicInt_pow p a u) k c hc

/- English proof (translation)
Use `(sub_eq_zero.mp (eq_zero_of_forall_mem_principalFiltration fun k ↦ ?_))` and prove the remaining obligations. Take `⟨c, hc, hl⟩` from `h k`. Use `sub_mem (padicIntSMul_spec p a u hc) hl` as an intermediate fact. Simplify using `using this`.
-/
theorem padicIntSMul_eq_of {a : ℤ_[p]} {u l : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k : ℕ, ∃ c : ℤ, (p : ℤ_[p]) ^ k ∣ a - c ∧ l - c • u ∈ principalFiltration K k) :
    padicIntSMul p a u = l := by
  refine (sub_eq_zero.mp (eq_zero_of_forall_mem_principalFiltration fun k ↦ ?_))
  obtain ⟨c, hc, hl⟩ := h k
  have := sub_mem (padicIntSMul_spec p a u hc) hl
  simpa using this

noncomputable instance instModulePadicInt : Module ℤ_[p] (Additive (unitFiltrationUnits K 1)) where
  smul := padicIntSMul p
  one_smul u := padicIntSMul_eq_of p fun k ↦ ⟨1, by simp, by simp⟩
  mul_smul a b u := by
    show padicIntSMul p (a * b) u = padicIntSMul p a (padicIntSMul p b u)
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have ha := dvd_sub_appr p k a
      have hb := dvd_sub_appr p k b
      have : a * b - (((((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ) : ℤ)) : ℤ_[p]) =
          a * (b - ((b.appr k : ℕ) : ℤ)) + ((b.appr k : ℕ) : ℤ) * (a - ((a.appr k : ℕ) : ℤ)) := by
        push_cast; ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right ha _)
    · have h1 := padicIntSMul_spec p a (padicIntSMul p b u) (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a (padicIntSMul p b u) -
          (((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a (padicIntSMul p b u) - ((a.appr k : ℕ) : ℤ) • padicIntSMul p b u) +
            ((a.appr k : ℕ) : ℤ) • (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [mul_zsmul, zsmul_sub]; abel
      rw [this]
      exact add_mem h1 (zsmul_mem h2 _)
  smul_zero a := padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, by simp⟩
  smul_add a u v := by
    show padicIntSMul p a (u + v) = padicIntSMul p a u + padicIntSMul p a v
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, ?_⟩
    have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
    have h2 := padicIntSMul_spec p a v (dvd_sub_appr p k a)
    have : padicIntSMul p a u + padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • (u + v) =
        (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
          (padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • v) := by
      rw [zsmul_add]; abel
    rw [this]
    exact add_mem h1 h2
  add_smul a b u := by
    show padicIntSMul p (a + b) u = padicIntSMul p a u + padicIntSMul p b u
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have := dvd_add (dvd_sub_appr p k a) (dvd_sub_appr p k b)
      convert this using 1
      push_cast; ring
    · have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a u + padicIntSMul p b u -
          (((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
            (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [add_zsmul]; abel
      rw [this]
      exact add_mem h1 h2
  zero_smul u := padicIntSMul_eq_of p fun k ↦ ⟨0, by simp, by simp⟩

end Module

section ModuleProps

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem padicInt_smul_def (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    a • u = padicIntSMul p a u := rfl

/- English proof (translation)
The claim follows from `padicIntSMul_spec p a u hc`.
-/
theorem smul_sub_intCast_smul_mem {a : ℤ_[p]} {k : ℕ} {c : ℤ} (hc : (p : ℤ_[p]) ^ k ∣ a - c)
    (u : Additive (unitFiltrationUnits K 1)) : a • u - c • u ∈ principalFiltration K k :=
  padicIntSMul_spec p a u hc

/- English proof (translation)
The claim follows from `padicIntSMul_eq_of p fun k ↦ ⟨c, by simp, by simp⟩`.
-/
theorem intCast_smul (c : ℤ) (u : Additive (unitFiltrationUnits K 1)) :
    ((c : ℤ_[p])) • u = c • u :=
  padicIntSMul_eq_of p fun k ↦ ⟨c, by simp, by simp⟩

/- English proof (translation)
Use `intCast_smul p (n : ℤ) u` as an intermediate fact. Simplify using `using this`.
-/
theorem natCast_smul (n : ℕ) (u : Additive (unitFiltrationUnits K 1)) :
    ((n : ℤ_[p])) • u = n • u := by
  have := intCast_smul p (n : ℤ) u
  simpa using this

/- English proof (translation)
Use `smul_sub_intCast_smul_mem p (c := 0) (by simpa using ha) u` as an intermediate fact. Simplify using `using this`.
-/
theorem smul_mem_of_dvd {a : ℤ_[p]} {k : ℕ} (ha : (p : ℤ_[p]) ^ k ∣ a)
    (u : Additive (unitFiltrationUnits K 1)) : a • u ∈ principalFiltration K k := by
  have := smul_sub_intCast_smul_mem p (c := 0) (by simpa using ha) u
  simpa using this

/- English proof (translation)
Establish `h1` using `smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u`. Establish `h2 : ((a.appr k : ℕ) : ℤ) • u ∈ principalFiltration K k` using `zsmul_mem hu _`. Simplify using `using add_mem h1 h2`.
-/
theorem smul_mem_principalFiltration (a : ℤ_[p]) {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : a • u ∈ principalFiltration K k := by
  have h1 := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h2 : ((a.appr k : ℕ) : ℤ) • u ∈ principalFiltration K k := zsmul_mem hu _
  simpa using add_mem h1 h2

/- English proof (translation)
Establish `h1 : 𝓝 (0 : Additive (unitFiltrationUnits K 1)) = Filter.comap (fun u : Additive (unitFiltrationUnits K 1) ↦ ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ)) (𝓝 1)` using `nhds_subtype _ (1 : unitFiltrationUnits K 1)`. Rewrite using `[h1]`. Use `(hasBasis_nhds_one_unitFiltrationUnits.comap _).to_hasBasis (fun n _ ↦ ⟨n, trivial, fun u hu ↦ unitFiltrationUnits_antitone (Nat.le_succ n) hu⟩) (fun k _ ↦ ⟨k + 1, trivial, fun u hu ↦ hu⟩)` and prove the remaining obligations.
-/
theorem hasBasis_nhds_zero_principalFiltration :
    (𝓝 (0 : Additive (unitFiltrationUnits K 1))).HasBasis (fun _ ↦ True)
      (fun k ↦ (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1)))) := by
  have h1 : 𝓝 (0 : Additive (unitFiltrationUnits K 1)) =
      Filter.comap (fun u : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ)) (𝓝 1) :=
    nhds_subtype _ (1 : unitFiltrationUnits K 1)
  rw [h1]
  refine (hasBasis_nhds_one_unitFiltrationUnits.comap _).to_hasBasis
    (fun n _ ↦ ⟨n, trivial, fun u hu ↦ unitFiltrationUnits_antitone (Nat.le_succ n) hu⟩)
    (fun k _ ↦ ⟨k + 1, trivial, fun u hu ↦ hu⟩)

/- English proof (translation)
The claim follows from `hasBasis_nhds_zero_principalFiltration.mem_of_mem trivial`.
-/
theorem principalFiltration_mem_nhds (k : ℕ) :
    (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1))) ∈ 𝓝 0 :=
  hasBasis_nhds_zero_principalFiltration.mem_of_mem trivial

instance continuousSMul_padicInt_principalUnits : ContinuousSMul ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  obtain ⟨a0, u0⟩ := x
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
    hasBasis_nhds_zero_principalFiltration.tendsto_right_iff]
  intro k _
  have h1 : {a : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ a - a0} ∈ 𝓝 a0 := by
    have hr : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      positivity
    refine Filter.mem_of_superset (Metric.closedBall_mem_nhds a0 hr) fun a ha ↦ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      Ideal.mem_span_singleton] at ha
    exact ha
  have h2 : {u : Additive (unitFiltrationUnits K 1) | u - u0 ∈ principalFiltration K k} ∈ 𝓝 u0 := by
    have ht : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 0) := by
      have : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 (u0 - u0)) :=
        tendsto_id.sub tendsto_const_nhds
      rwa [sub_self] at this
    exact ht (principalFiltration_mem_nhds k)
  filter_upwards [prod_mem_nhds h1 h2] with x hx
  obtain ⟨a, u⟩ := x
  obtain ⟨ha, hu⟩ := hx
  have : a • u - a0 • u0 = (a - a0) • u + a0 • (u - u0) := by rw [sub_smul, smul_sub]; abel
  show a • u - a0 • u0 ∈ principalFiltration K k
  rw [this]
  exact add_mem (smul_mem_of_dvd p ha u) (smul_mem_principalFiltration p a0 hu)

end ModuleProps

end GroundTheory.LocalField
