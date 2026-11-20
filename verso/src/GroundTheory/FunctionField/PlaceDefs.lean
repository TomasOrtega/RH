import Mathlib

namespace GroundTheory.FunctionField

open IntermediateField

open scoped WithZero

section FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

class IsFunctionField : Prop where
  exists_transcendental_finiteDimensional :
    ∃ x : K, Transcendental k x ∧ FiniteDimensional (IntermediateField.adjoin k {x}) K

variable {k K}

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Rewrite using `[isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]`. Use `⟨(algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).2 hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Subtype.range_coe]`. Establish `: Algebra.IsAlgebraic (IntermediateField.adjoin k {y}) K` using `Algebra.IsAlgebraic.of_finite _ _`. Conclude with `Algebra.IsAlgebraic.trans (Algebra.adjoin k {y}) (IntermediateField.adjoin k {y}) K`.
-/
theorem isTranscendenceBasis_singleton {y : K} (hy : Transcendental k y)
    (hfin : FiniteDimensional (IntermediateField.adjoin k {y}) K) :
    IsTranscendenceBasis k ((↑) : ({y} : Set K) → K) := by
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
  refine ⟨(algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).2 hy, ?_⟩
  rw [Subtype.range_coe]
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k {y}) K :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.trans (Algebra.adjoin k {y}) (IntermediateField.adjoin k {y}) K

/- English proof (translation)
Take `⟨y, hy, hfin⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Rewrite using `[← (isTranscendenceBasis_singleton hy hfin).cardinalMk_eq_trdeg, Cardinal.mk_singleton]`.
-/
theorem trdeg_eq_one [IsFunctionField k K] : Algebra.trdeg k K = 1 := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  rw [← (isTranscendenceBasis_singleton hy hfin).cardinalMk_eq_trdeg, Cardinal.mk_singleton]

/- English proof (translation)
Take `⟨y, -, hfin⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Establish `: Algebra.EssFiniteType k (IntermediateField.adjoin k {y})` using `IntermediateField.essFiniteType_iff.2 (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton y))`. Conclude with `Algebra.EssFiniteType.comp k (IntermediateField.adjoin k {y}) K`.
-/
theorem essFiniteType [IsFunctionField k K] : Algebra.EssFiniteType k K := by
  obtain ⟨y, -, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have : Algebra.EssFiniteType k (IntermediateField.adjoin k {y}) :=
    IntermediateField.essFiniteType_iff.2 (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton y))
  exact Algebra.EssFiniteType.comp k (IntermediateField.adjoin k {y}) K

/- English proof (translation)
Establish `hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K)` using `AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx) (by rw [trdeg_eq_one, Cardinal.mk_singleton])`. Establish `halg` using `hbx.isAlgebraic_field`. Rewrite `halg` using `[Subtype.range_coe]`. Use `essFiniteType (k := k) (K := K)` as an intermediate fact. Establish `: Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K` using `Algebra.EssFiniteType.of_comp k _ K`.

Conclude with `Algebra.finite_of_essFiniteType_of_isAlgebraic`.
-/
theorem finiteDimensional_adjoin [IsFunctionField k K] {x : K} (hx : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k {x}) K := by
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [trdeg_eq_one, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end FunctionField

open Polynomial

section Place

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

@[ext]
structure Place where

  ring : ValuationSubring K
  ne_top : ring ≠ ⊤
  algebraMap_mem : ∀ c : k, algebraMap k K c ∈ ring

namespace Place

variable {k K} (v : Place k K)

instance : Algebra k v.ring :=
  (RingHom.codRestrict (algebraMap k K) v.ring v.algebraMap_mem).toAlgebra

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap_apply (c : k) : ((algebraMap k v.ring c : v.ring) : K) = algebraMap k K c :=
  rfl

instance : IsScalarTower k v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev ResidueField := IsLocalRing.ResidueField v.ring

/- English proof (translation)
The claim follows from `(v.ring.valuation_eq_one_iff (algebraMap k v.ring c)).1 ((IsUnit.mk0 c hc).map _)`.
-/
theorem valuation_algebraMap {c : k} (hc : c ≠ 0) : v.ring.valuation (algebraMap k K c) = 1 :=
  (v.ring.valuation_eq_one_iff (algebraMap k v.ring c)).1 ((IsUnit.mk0 c hc).map _)

/- English proof (translation)
Establish `h : aeval x p = algebraMap v.ring K (aeval (⟨x, hx⟩ : v.ring) p)` using `Polynomial.aeval_algebraMap_apply K (⟨x, hx⟩ : v.ring) p`. Rewrite using `[h]`. Conclude with `v.ring.valuation_le_one _`.
-/
theorem valuation_aeval_le_one {x : K} (hx : x ∈ v.ring) (p : k[X]) :
    v.ring.valuation (aeval x p) ≤ 1 := by
  have h : aeval x p = algebraMap v.ring K (aeval (⟨x, hx⟩ : v.ring) p) :=
    Polynomial.aeval_algebraMap_apply K (⟨x, hx⟩ : v.ring) p
  rw [h]
  exact v.ring.valuation_le_one _

/- English proof (translation)
Rewrite `h`, the goal using `[← v.valuation_algebraMap ha]`. Conclude with `Valuation.map_eq_of_sub_lt _ h`.
-/
theorem valuation_eq_one_of_sub_lt {z : K} {a : k} (ha : a ≠ 0)
    (h : v.ring.valuation (z - algebraMap k K a) < 1) : v.ring.valuation z = 1 := by
  rw [← v.valuation_algebraMap ha] at h ⊢
  exact Valuation.map_eq_of_sub_lt _ h

/- English proof (translation)
Establish `hxO : x ∈ v.ring` using `(v.ring.valuation_le_one_iff x).1 hx.le`. Use `revert hp`. Proceed by induction on `p using Polynomial.recOnHorner with`. Consider the case `M0 => intro h`. Conclude with `absurd rfl h`.

Consider the case `MC p a hp0 ha _`. Introduce `_`. Use `⟨0, a, ha, ?_⟩` and prove the remaining obligations. Take `⟨q, rfl⟩ : X ∣ p` from `Polynomial.X_dvd_iff.2 hp0`. Rewrite using `[pow_zero, div_one, map_add, aeval_C, add_sub_cancel_right, map_mul, aeval_X, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Consider the case `MX p hp0 ih`. Introduce `_`. Take `⟨m, a, ha, h⟩` from `ih hp0`. Use `⟨m + 1, a, ha, ?_⟩` and prove the remaining obligations.

Establish `: aeval x (p * X) / x ^ (m + 1) = aeval x p / x ^ m`. Rewrite using `[map_mul, aeval_X, pow_succ, mul_div_mul_right _ _ hx0]`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem exists_aeval_div_pow {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) (p : k[X])
    (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ a : k, a ≠ 0 ∧ v.ring.valuation (aeval x p / x ^ m - algebraMap k K a) < 1 := by
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  revert hp
  induction p using Polynomial.recOnHorner with
  | M0 => intro h; exact absurd rfl h
  | MC p a hp0 ha _ =>
    intro _
    refine ⟨0, a, ha, ?_⟩
    obtain ⟨q, rfl⟩ : X ∣ p := Polynomial.X_dvd_iff.2 hp0
    rw [pow_zero, div_one, map_add, aeval_C, add_sub_cancel_right, map_mul, aeval_X, map_mul]
    calc v.ring.valuation x * v.ring.valuation (aeval x q) ≤ v.ring.valuation x * 1 :=
          mul_le_mul' le_rfl (v.valuation_aeval_le_one hxO q)
      _ < 1 := by rwa [mul_one]
  | MX p hp0 ih =>
    intro _
    obtain ⟨m, a, ha, h⟩ := ih hp0
    refine ⟨m + 1, a, ha, ?_⟩
    have : aeval x (p * X) / x ^ (m + 1) = aeval x p / x ^ m := by
      rw [map_mul, aeval_X, pow_succ, mul_div_mul_right _ _ hx0]
    rwa [this]

/- English proof (translation)
Introduce and unpack `⟨p, hp, hpx⟩`. Take `⟨m, a, ha, h⟩` from `v.exists_aeval_div_pow hx0 hx p hp`. Establish `h1` using `v.valuation_eq_one_of_sub_lt ha h`. Rewrite `h1` using `[hpx, zero_div, map_zero]`. Conclude with `zero_ne_one h1`.
-/
theorem transcendental_of_valuation_lt_one {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) :
    Transcendental k x := by
  rintro ⟨p, hp, hpx⟩
  obtain ⟨m, a, ha, h⟩ := v.exists_aeval_div_pow hx0 hx p hp
  have h1 := v.valuation_eq_one_of_sub_lt ha h
  rw [hpx, zero_div, map_zero] at h1
  exact zero_ne_one h1

/- English proof (translation)
Take `⟨r, s, rfl⟩` from `(IntermediateField.mem_adjoin_simple_iff k c).1 hc`. Establish `hr : r ≠ 0` using `by rintro rfl; simp at hc0`. Establish `hs : s ≠ 0` using `by rintro rfl; simp at hc0`. Take `⟨m₁, a₁, ha₁, h₁⟩` from `v.exists_aeval_div_pow hx0 hx r hr`. Take `⟨m₂, a₂, ha₂, h₂⟩` from `v.exists_aeval_div_pow hx0 hx s hs`.

Establish `hz₂` using `v.valuation_eq_one_of_sub_lt ha₂ h₂`. Establish `hs0 : aeval x s ≠ 0`. Introduce `h`. Rewrite `hz₂` using `[h, zero_div, map_zero]`. Conclude with `zero_ne_one hz₂`.

Establish `hz₂0 : aeval x s / x ^ m₂ ≠ 0` using `div_ne_zero hs0 (pow_ne_zero _ hx0)`. Establish `ha₂' : algebraMap k K a₂ ≠ 0` using `(_root_.map_ne_zero _).2 ha₂`. Use `⟨(m₁ : ℤ) - m₂, a₁ / a₂, div_ne_zero ha₁ ha₂, ?_⟩` and prove the remaining obligations. Establish `key : aeval x r / aeval x s / x ^ ((m₁ : ℤ) - m₂) - algebraMap k K (a₁ / a₂) = ((aeval x r / x ^ m₁ - algebraMap k K a₁) * algebraMap k K a₂ - algebraMap k K a₁ * (aeval x s / x ^ m₂ - algebraMap k K a₂)) / (aeval x s / x ^ m₂ * algebraMap k K a₂)`. Rewrite using `[map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key, map_div₀, map_mul, hz₂, v.valuation_algebraMap ha₂, one_mul, div_one]`. Use `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul, v.valuation_algebraMap ha₂, mul_one]`.

Conclude with `h₁`. Rewrite using `[map_mul, v.valuation_algebraMap ha₁, one_mul]`. Conclude with `h₂`.
-/
theorem exists_zpow_of_mem_adjoin {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) {c : K}
    (hc : c ∈ IntermediateField.adjoin k {x}) (hc0 : c ≠ 0) :
    ∃ m : ℤ, ∃ a : k, a ≠ 0 ∧ v.ring.valuation (c / x ^ m - algebraMap k K a) < 1 := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k c).1 hc
  have hr : r ≠ 0 := by rintro rfl; simp at hc0
  have hs : s ≠ 0 := by rintro rfl; simp at hc0
  obtain ⟨m₁, a₁, ha₁, h₁⟩ := v.exists_aeval_div_pow hx0 hx r hr
  obtain ⟨m₂, a₂, ha₂, h₂⟩ := v.exists_aeval_div_pow hx0 hx s hs
  have hz₂ := v.valuation_eq_one_of_sub_lt ha₂ h₂
  have hs0 : aeval x s ≠ 0 := by
    intro h; rw [h, zero_div, map_zero] at hz₂; exact zero_ne_one hz₂
  have hz₂0 : aeval x s / x ^ m₂ ≠ 0 := div_ne_zero hs0 (pow_ne_zero _ hx0)
  have ha₂' : algebraMap k K a₂ ≠ 0 := (_root_.map_ne_zero _).2 ha₂
  refine ⟨(m₁ : ℤ) - m₂, a₁ / a₂, div_ne_zero ha₁ ha₂, ?_⟩
  have key : aeval x r / aeval x s / x ^ ((m₁ : ℤ) - m₂) - algebraMap k K (a₁ / a₂) =
      ((aeval x r / x ^ m₁ - algebraMap k K a₁) * algebraMap k K a₂ -
          algebraMap k K a₁ * (aeval x s / x ^ m₂ - algebraMap k K a₂)) /
        (aeval x s / x ^ m₂ * algebraMap k K a₂) := by
    rw [map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]
    field_simp
    ring
  rw [key, map_div₀, map_mul, hz₂, v.valuation_algebraMap ha₂, one_mul, div_one]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, v.valuation_algebraMap ha₂, mul_one]; exact h₁
  · rw [map_mul, v.valuation_algebraMap ha₁, one_mul]; exact h₂

/- English proof (translation)
Take `⟨m, a, ha, h⟩` from `v.exists_zpow_of_mem_adjoin hx0 hx hc hc0`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `h1` using `v.valuation_eq_one_of_sub_lt ha h`. Rewrite `h1` using `[map_div₀, map_zpow₀]`. Establish `hxm : v.ring.valuation x ^ m ≠ 0` using `zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hx0)`.

Conclude with `(div_eq_one_iff_eq hxm).1 h1`.
-/
theorem exists_valuation_eq_zpow {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) {c : K}
    (hc : c ∈ IntermediateField.adjoin k {x}) (hc0 : c ≠ 0) :
    ∃ m : ℤ, v.ring.valuation c = v.ring.valuation x ^ m := by
  obtain ⟨m, a, ha, h⟩ := v.exists_zpow_of_mem_adjoin hx0 hx hc hc0
  refine ⟨m, ?_⟩
  have h1 := v.valuation_eq_one_of_sub_lt ha h
  rw [map_div₀, map_zpow₀] at h1
  have hxm : v.ring.valuation x ^ m ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hx0)
  exact (div_eq_one_iff_eq hxm).1 h1

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨z, hz⟩ : ∃ z, z ∉ v.ring := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `v.ne_top (eq_top_iff.2 fun z _ => h z)`. Establish `hz0 : z ≠ 0` using `fun h => hz (h ▸ v.ring.zero_mem)`.

Conclude with `⟨z⁻¹, inv_ne_zero hz0, v.ring.mem_nonunits_iff.1 (v.ring.inv_mem_nonunits_iff.2 (Or.inr hz))⟩`.
-/
theorem exists_valuation_lt_one_ne_zero : ∃ x : K, x ≠ 0 ∧ v.ring.valuation x < 1 := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ v.ring := by
    by_contra h
    push Not at h
    exact v.ne_top (eq_top_iff.2 fun z _ => h z)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ v.ring.zero_mem)
  exact ⟨z⁻¹, inv_ne_zero hz0,
    v.ring.mem_nonunits_iff.1 (v.ring.inv_mem_nonunits_iff.2 (Or.inr hz))⟩

/- English proof (translation)
Use `set V := v.ring.valuation`. Establish `hX0 : 0 < V x` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)`. Establish `aux : ∀ i j (m n : ℤ), m < n → V (a i) * V x ^ m = V (a j) * V x ^ n → False`. Introduce `i j m n hmn h`. Establish `h1 : V x ^ n ≤ V x ^ (m + 1)` using `(zpow_right_strictAnti₀ hX0 hx).antitone (by omega)`.

Establish `h2 : V (a i) * V x ^ m ≤ V x * V x ^ m`. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation. Establish `hm : 0 < V x ^ m` using `zpow_pos hX0 m`. Conclude with `absurd (le_of_mul_le_mul_right h2 hm) (not_le.2 (hlow i))`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨i₀, hi₀⟩` from `hne`.

Set `s` to `Finset.univ.filter fun i => g i ≠ 0`. Establish `hs : s.Nonempty` using `⟨i₀, by simp [s, hi₀]⟩`. Take `⟨j, hj, hmax⟩` from `s.exists_max_image (fun i => V ((g i : K) * a i)) hs`. Establish `hterm : ∀ i ∈ s, ∃ m : ℤ, V ((g i : K) * a i) = V (a i) * V x ^ m`. Introduce `i hi`.

Establish `hgi : (g i : K) ≠ 0`. Establish `: g i ≠ 0` using `by simpa [s] using hi`. Conclude with `fun h => this (Subtype.ext h)`. Take `⟨m, hm⟩` from `v.exists_valuation_eq_zpow hx0 hx (g i).2 hgi`. Conclude with `⟨m, by rw [map_mul, hm, mul_comm]⟩`.

Establish `hlt : ∀ i ∈ s \ {j}, V ((g i : K) * a i) < V ((g j : K) * a j)`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Use `lt_of_le_of_ne (hmax i hi.1) ?_` and prove the remaining obligations. Introduce `heq`.

Take `⟨m, hm⟩` from `hterm i hi.1`. Take `⟨n, hn⟩` from `hterm j hj`. Rewrite `heq` using `[hm, hn]`. Break down `lt_trichotomy m n with h | h | h` into its components or cases. Conclude with `aux i j m n h heq`.

Substitute `h` using the available equality. Conclude with `hi.2 (hinj (mul_right_cancel₀ (zpow_ne_zero _ hX0.ne') heq))`. Conclude with `aux j i n m h heq.symm`. Establish `hsum : ∑ i, g i • a i = ∑ i ∈ s, (g i : K) * a i`. Rewrite using `[Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Use `push Not at h`. Rewrite using `[h, zero_smul]`.

Establish `hval` using `V.map_sum_eq_of_lt hj hlt`. Rewrite `hval` using `[← hsum, hg, map_zero]`. Take `⟨n, hn⟩` from `hterm j hj`. Rewrite `hval` using `[hn]`. Establish `haj : V (a j) ≠ 0` using `(lt_trans hX0 (hlow j)).ne'`.

Conclude with `mul_ne_zero haj (zpow_ne_zero _ hX0.ne') hval.symm`.
-/
theorem linearIndependent_of_valuation {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1)
    {ι : Type*} [Fintype ι] (a : ι → K)
    (hlow : ∀ i, v.ring.valuation x < v.ring.valuation (a i))
    (hup : ∀ i, v.ring.valuation (a i) ≤ 1)
    (hinj : Function.Injective fun i => v.ring.valuation (a i)) :
    LinearIndependent (IntermediateField.adjoin k {x}) a := by
  classical
  set V := v.ring.valuation
  have hX0 : 0 < V x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  have aux : ∀ i j (m n : ℤ), m < n → V (a i) * V x ^ m = V (a j) * V x ^ n → False := by
    intro i j m n hmn h
    have h1 : V x ^ n ≤ V x ^ (m + 1) := (zpow_right_strictAnti₀ hX0 hx).antitone (by omega)
    have h2 : V (a i) * V x ^ m ≤ V x * V x ^ m := by
      rw [h]
      calc V (a j) * V x ^ n ≤ 1 * V x ^ (m + 1) := mul_le_mul' (hup j) h1
        _ = V x * V x ^ m := by rw [one_mul, zpow_add_one₀ hX0.ne', mul_comm]
    have hm : 0 < V x ^ m := zpow_pos hX0 m
    exact absurd (le_of_mul_le_mul_right h2 hm) (not_le.2 (hlow i))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  let s := Finset.univ.filter fun i => g i ≠ 0
  have hs : s.Nonempty := ⟨i₀, by simp [s, hi₀]⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => V ((g i : K) * a i)) hs
  have hterm : ∀ i ∈ s, ∃ m : ℤ, V ((g i : K) * a i) = V (a i) * V x ^ m := by
    intro i hi
    have hgi : (g i : K) ≠ 0 := by
      have : g i ≠ 0 := by simpa [s] using hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨m, hm⟩ := v.exists_valuation_eq_zpow hx0 hx (g i).2 hgi
    exact ⟨m, by rw [map_mul, hm, mul_comm]⟩
  have hlt : ∀ i ∈ s \ {j}, V ((g i : K) * a i) < V ((g j : K) * a j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    refine lt_of_le_of_ne (hmax i hi.1) ?_
    intro heq
    obtain ⟨m, hm⟩ := hterm i hi.1
    obtain ⟨n, hn⟩ := hterm j hj
    rw [hm, hn] at heq
    rcases lt_trichotomy m n with h | h | h
    · exact aux i j m n h heq
    · subst h
      exact hi.2 (hinj (mul_right_cancel₀ (zpow_ne_zero _ hX0.ne') heq))
    · exact aux j i n m h heq.symm
  have hsum : ∑ i, g i • a i = ∑ i ∈ s, (g i : K) * a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [h, zero_smul]
  have hval := V.map_sum_eq_of_lt hj hlt
  rw [← hsum, hg, map_zero] at hval
  obtain ⟨n, hn⟩ := hterm j hj
  rw [hn] at hval
  have haj : V (a j) ≠ 0 := (lt_trans hX0 (hlow j)).ne'
  exact mul_ne_zero haj (zpow_ne_zero _ hX0.ne') hval.symm

/- English proof (translation)
Use `set V := v.ring.valuation`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Take `⟨i₀, hi₀⟩` from `hne`. Take `⟨j, -, hmax⟩` from `Finset.univ.exists_max_image (fun i => V (g i : K)) ⟨i₀, Finset.mem_univ _⟩`. Establish `hgi₀ : (g i₀ : K) ≠ 0` using `fun h => hi₀ (Subtype.ext h)`. Establish `hgj : (g j : K) ≠ 0`. Introduce `h`.

Use `hmax i₀ (Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `hgi₀ ((Valuation.zero_iff _).1 (le_antisymm this zero_le))`. Establish `hVj : 0 < V (g j : K)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hgj)`. Establish `hle : ∀ i, V ((g i : K) / g j) ≤ 1` using `fun i => by`.

Rewrite using `[map_div₀]`. Conclude with `(div_le_one₀ hVj).2 (hmax i (Finset.mem_univ _))`. Establish `hh : ∀ i, ∃ b : k, V ((g i : K) / g j - algebraMap k K b) < 1`. Introduce `i`. Break down `(hle i).lt_or_eq with hlt | heq` into its components or cases.

Conclude with `⟨0, by rwa [map_zero, sub_zero]⟩`. Establish `hne : (g i : K) / g j ≠ 0`. Introduce `h`. Rewrite `heq` using `[h, map_zero]`. Conclude with `zero_ne_one heq`.

Establish `hmem : (g i : K) / g j ∈ IntermediateField.adjoin k {x}` using `div_mem (g i).2 (g j).2`. Take `⟨m, a, ha, h⟩` from `v.exists_zpow_of_mem_adjoin hx0 hx hmem hne`. Establish `h1` using `v.valuation_eq_one_of_sub_lt ha h`. Rewrite `h1` using `[map_div₀, map_zpow₀, heq, one_div, inv_eq_one, zpow_eq_one_iff_right₀ zero_le hx.ne]`. Substitute `h1` using the available equality.

Conclude with `⟨a, by simpa using h⟩`. Use `choose b hb using hh`. Set `y : ι → v.ring` to `fun i => ⟨(g i : K) / g j, (v.ring.valuation_le_one_iff _).1 (hle i)⟩`. Establish `hres : ∀ i, IsLocalRing.residue v.ring (y i) = algebraMap k v.ResidueField (b i)`. Introduce `i`.

Rewrite using `[IsScalarTower.algebraMap_apply k v.ring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, v.ring.valuation_lt_one_iff]`. Conclude with `hb i`. Establish `hsum0 : ∑ i, y i * z i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ∑ i, (g i : K) / g j * (z i : K) = (∑ i, g i • (z i : K)) / g j`.

Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Simplify using `only [IntermediateField.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify `this` using `[y, hg]`. Establish `hcomb : ∑ i, b i • IsLocalRing.residue v.ring (z i) = 0`. Use `congrArg (IsLocalRing.residue v.ring) hsum0` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hres, Algebra.smul_def]`. Establish `hbj` using `(Fintype.linearIndependent_iff.1 hz) b hcomb j`. Use `hb j` as an intermediate fact. Rewrite `this` using `[hbj, map_zero, sub_zero, div_self hgj, map_one]`.

Conclude with `lt_irrefl _ this`.
-/
theorem linearIndependent_of_residue {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1)
    {ι : Type*} [Fintype ι] (z : ι → v.ring)
    (hz : LinearIndependent k fun i => IsLocalRing.residue v.ring (z i)) :
    LinearIndependent (IntermediateField.adjoin k {x}) fun i => (z i : K) := by
  classical
  set V := v.ring.valuation
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hmax⟩ := Finset.univ.exists_max_image (fun i => V (g i : K)) ⟨i₀, Finset.mem_univ _⟩
  have hgi₀ : (g i₀ : K) ≠ 0 := fun h => hi₀ (Subtype.ext h)
  have hgj : (g j : K) ≠ 0 := by
    intro h
    have := hmax i₀ (Finset.mem_univ _)
    rw [h, map_zero] at this
    exact hgi₀ ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hVj : 0 < V (g j : K) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hgj)
  have hle : ∀ i, V ((g i : K) / g j) ≤ 1 := fun i => by
    rw [map_div₀]; exact (div_le_one₀ hVj).2 (hmax i (Finset.mem_univ _))
  have hh : ∀ i, ∃ b : k, V ((g i : K) / g j - algebraMap k K b) < 1 := by
    intro i
    rcases (hle i).lt_or_eq with hlt | heq
    · exact ⟨0, by rwa [map_zero, sub_zero]⟩
    · have hne : (g i : K) / g j ≠ 0 := by
        intro h; rw [h, map_zero] at heq; exact zero_ne_one heq
      have hmem : (g i : K) / g j ∈ IntermediateField.adjoin k {x} := div_mem (g i).2 (g j).2
      obtain ⟨m, a, ha, h⟩ := v.exists_zpow_of_mem_adjoin hx0 hx hmem hne
      have h1 := v.valuation_eq_one_of_sub_lt ha h
      rw [map_div₀, map_zpow₀, heq, one_div, inv_eq_one,
        zpow_eq_one_iff_right₀ zero_le hx.ne] at h1
      subst h1
      exact ⟨a, by simpa using h⟩
  choose b hb using hh
  let y : ι → v.ring := fun i => ⟨(g i : K) / g j, (v.ring.valuation_le_one_iff _).1 (hle i)⟩
  have hres : ∀ i, IsLocalRing.residue v.ring (y i) = algebraMap k v.ResidueField (b i) := by
    intro i
    rw [IsScalarTower.algebraMap_apply k v.ring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, v.ring.valuation_lt_one_iff]
    exact hb i
  have hsum0 : ∑ i, y i * z i = 0 := by
    apply Subtype.ext
    have : ∑ i, (g i : K) / g j * (z i : K) = (∑ i, g i • (z i : K)) / g j := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def]
      simp only [IntermediateField.algebraMap_apply]
      ring
    simpa [y, hg] using this
  have hcomb : ∑ i, b i • IsLocalRing.residue v.ring (z i) = 0 := by
    have := congrArg (IsLocalRing.residue v.ring) hsum0
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hres, Algebra.smul_def]
  have hbj := (Fintype.linearIndependent_iff.1 hz) b hcomb j
  have := hb j
  rw [hbj, map_zero, sub_zero, div_self hgj, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Rewrite using `[isNoetherianRing_iff, isNoetherian_iff', WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]`. Use `⟨fun f => ?_⟩` and prove the remaining obligations. Establish `hf : ∀ n, f n < f (n + 1)` using `fun n => f.map_rel_iff.2 (Nat.lt_succ_self n)`. Use `choose b hb1 hb2 using fun n => SetLike.exists_of_lt (hf n)`. Use `set V := v.ring.valuation`.

Establish `hstep : ∀ n, V (b n : K) < V (b (n + 1) : K)`. Introduce `n`. Assume the negation of the conclusion as `hle`. Use `push Not at hle`. Apply `hb2 (n + 1)` to reduce the goal to its premises.

Distinguish the cases in `h0 : (b n : K) = 0`. Establish `h1 : (b (n + 1) : K) = 0`. Rewrite `hle` using `[h0, map_zero]`. Conclude with `(Valuation.zero_iff _).1 (le_antisymm hle zero_le)`. Rewrite using `[show b (n + 1) = 0 from Subtype.ext h1]`.

Conclude with `zero_mem _`. Establish `hc : (b (n + 1) : K) / b n ∈ v.ring`. Rewrite using `[← v.ring.valuation_le_one_iff, map_div₀]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))).2 hle`. Establish `heq : b (n + 1) = b n * ⟨_, hc⟩` using `Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `(b (n + 1) : K) = b n * ((b (n + 1) : K) / b n)`. Rewrite using `[mul_div_cancel₀ _ h0])`. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_right _ _ (hb1 n)`. Establish `hmono : StrictMono fun n => V (b n : K)` using `strictMono_nat_of_lt_succ hstep`.

Establish `hb0 : (b 0 : K) ≠ 0`. Introduce `h`. Apply `hb2 0` to reduce the goal to its premises. Rewrite using `[show b 0 = 0 from Subtype.ext h]`. Conclude with `zero_mem _`.

Establish `hb0lt : V (b 0 : K) < 1` using `lt_of_lt_of_le (hstep 0) (v.ring.valuation_le_one _)`. Use `finiteDimensional_adjoin (v.transcendental_of_valuation_lt_one hb0 hb0lt)` as an intermediate fact. Establish `hli` using `v.linearIndependent_of_valuation hb0 hb0lt (fun i : Fin (Module.finrank (IntermediateField.adjoin k {(b 0 : K)}) K + 1) => (b ((i : ℕ) + 1) : K)) (fun i => hmono (Nat.succ_pos _)) (fun i => v.ring.valuation_le_one _) (fun i j h => Fin.ext (by simpa using hmono.injective h))`. Establish `hcard` using `hli.fintype_card_le_finrank`. Rewrite `hcard` using `[Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isNoetherianRing [IsFunctionField k K] : IsNoetherianRing v.ring := by
  rw [isNoetherianRing_iff, isNoetherian_iff', WellFoundedGT, isWellFounded_iff,
    RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  have hf : ∀ n, f n < f (n + 1) := fun n => f.map_rel_iff.2 (Nat.lt_succ_self n)
  choose b hb1 hb2 using fun n => SetLike.exists_of_lt (hf n)
  set V := v.ring.valuation
  have hstep : ∀ n, V (b n : K) < V (b (n + 1) : K) := by
    intro n
    by_contra hle
    push Not at hle
    apply hb2 (n + 1)
    by_cases h0 : (b n : K) = 0
    · have h1 : (b (n + 1) : K) = 0 := by
        rw [h0, map_zero] at hle
        exact (Valuation.zero_iff _).1 (le_antisymm hle zero_le)
      rw [show b (n + 1) = 0 from Subtype.ext h1]
      exact zero_mem _
    · have hc : (b (n + 1) : K) / b n ∈ v.ring := by
        rw [← v.ring.valuation_le_one_iff, map_div₀]
        exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))).2 hle
      have heq : b (n + 1) = b n * ⟨_, hc⟩ := Subtype.ext (by
        change (b (n + 1) : K) = b n * ((b (n + 1) : K) / b n)
        rw [mul_div_cancel₀ _ h0])
      rw [heq]
      exact Ideal.mul_mem_right _ _ (hb1 n)
  have hmono : StrictMono fun n => V (b n : K) := strictMono_nat_of_lt_succ hstep
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    apply hb2 0
    rw [show b 0 = 0 from Subtype.ext h]
    exact zero_mem _
  have hb0lt : V (b 0 : K) < 1 := lt_of_lt_of_le (hstep 0) (v.ring.valuation_le_one _)
  have := finiteDimensional_adjoin (v.transcendental_of_valuation_lt_one hb0 hb0lt)
  have hli := v.linearIndependent_of_valuation hb0 hb0lt
    (fun i : Fin (Module.finrank (IntermediateField.adjoin k {(b 0 : K)}) K + 1) =>
      (b ((i : ℕ) + 1) : K))
    (fun i => hmono (Nat.succ_pos _)) (fun i => v.ring.valuation_le_one _)
    (fun i j h => Fin.ext (by simpa using hmono.injective h))
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

instance [IsFunctionField k K] : IsDiscreteValuationRing v.ring := by
  have hN := v.isNoetherianRing
  have : IsPrincipalIdealRing v.ring := ((IsBezout.TFAE (R := v.ring)).out 0 1).1 hN
  refine { (inferInstance : IsPrincipalIdealRing v.ring), (inferInstance : IsLocalRing v.ring) with
    not_a_field' := ?_ }
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  intro h
  have hmem : (⟨x, hxO⟩ : v.ring) ∈ IsLocalRing.maximalIdeal v.ring :=
    (v.ring.valuation_lt_one_iff _).2 hx
  rw [h, Ideal.mem_bot] at hmem
  exact hx0 (congrArg Subtype.val hmem)

instance [IsFunctionField k K] : FiniteDimensional k v.ResidueField := by
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have := finiteDimensional_adjoin (v.transcendental_of_valuation_lt_one hx0 hx)
  apply Module.rank_lt_aleph0_iff.1
  refine lt_of_le_of_lt
    (rank_le (n := Module.finrank (IntermediateField.adjoin k {x}) K) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0)
  choose z hz using fun r : v.ResidueField => IsLocalRing.residue_surjective r
  have hli := v.linearIndependent_of_residue hx0 hx (fun i : s => z i) (by simpa [hz] using hs)
  simpa using hli.fintype_card_le_finrank

noncomputable def deg : ℕ := Module.finrank k v.ResidueField

/- English proof (translation)
The claim follows from `Module.finrank_pos`.
-/
theorem deg_pos [IsFunctionField k K] : 0 < v.deg := Module.finrank_pos

section Valuation

variable [IsFunctionField k K]

def heightOneSpectrum : IsDedekindDomain.HeightOneSpectrum v.ring where
  asIdeal := IsLocalRing.maximalIdeal v.ring
  isPrime := (IsLocalRing.maximalIdeal.isMaximal v.ring).isPrime
  ne_bot := IsDiscreteValuationRing.not_a_field v.ring

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.ring :=
  rfl

noncomputable def valuation : Valuation K ℤᵐ⁰ := v.heightOneSpectrum.valuation K

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hx`. Establish `hx0 : x ≠ 0` using `fun h0 => hx (h0 ▸ v.ring.zero_mem)`. Establish `hinv : x⁻¹ ∈ v.ring.nonunits` using `v.ring.inv_mem_nonunits_iff.2 (Or.inr hx)`.

Take `⟨hr, hrm⟩` from `v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv`. Establish `hlt : v.valuation x⁻¹ < 1` using `(v.heightOneSpectrum.valuation_lt_one_iff_mem (K := K) ⟨x⁻¹, hr⟩).2 hrm`. Rewrite `hlt` using `[map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]`. Conclude with `absurd h (not_le.2 hlt)`. Introduce `hx`.

Conclude with `v.heightOneSpectrum.valuation_le_one (K := K) (⟨x, hx⟩ : v.ring)`.
-/
theorem valuation_le_one_iff (x : K) : v.valuation x ≤ 1 ↔ x ∈ v.ring := by
  constructor
  · intro h
    by_contra hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ v.ring.zero_mem)
    have hinv : x⁻¹ ∈ v.ring.nonunits := v.ring.inv_mem_nonunits_iff.2 (Or.inr hx)
    obtain ⟨hr, hrm⟩ := v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv
    have hlt : v.valuation x⁻¹ < 1 :=
      (v.heightOneSpectrum.valuation_lt_one_iff_mem (K := K) ⟨x⁻¹, hr⟩).2 hrm
    rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at hlt
    exact absurd h (not_le.2 hlt)
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (K := K) (⟨x, hx⟩ : v.ring)

/- English proof (translation)
The claim follows from `Valuation.isEquiv_iff_val_le_one.2 fun {x} => (v.valuation_le_one_iff x).trans (v.ring.valuation_le_one_iff x).symm`.
-/
theorem valuation_isEquiv : v.valuation.IsEquiv v.ring.valuation :=
  Valuation.isEquiv_iff_val_le_one.2 fun {x} =>
    (v.valuation_le_one_iff x).trans (v.ring.valuation_le_one_iff x).symm

/- English proof (translation)
The claim follows from `v.valuation_isEquiv.lt_one_iff_lt_one`.
-/
theorem valuation_lt_one_iff (x : K) : v.valuation x < 1 ↔ v.ring.valuation x < 1 :=
  v.valuation_isEquiv.lt_one_iff_lt_one

/- English proof (translation)
The claim follows from `v.valuation_isEquiv.eq_one_iff_eq_one.2 (v.valuation_algebraMap hc)`.
-/
theorem valuation_algebraMap' {c : k} (hc : c ≠ 0) : v.valuation (algebraMap k K c) = 1 :=
  v.valuation_isEquiv.eq_one_iff_eq_one.2 (v.valuation_algebraMap hc)

/- English proof (translation)
The claim follows from `IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v.heightOneSpectrum`.
-/
theorem valuation_surjective : Function.Surjective v.valuation :=
  IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v.heightOneSpectrum

noncomputable def ord (x : K) : ℤ := -WithZero.log (v.valuation x)

/- English proof (translation)
Rewrite using `[ord, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]`. Use the proof step `@[simp]`.
-/
theorem valuation_eq_exp_neg_ord {x : K} (hx : x ≠ 0) :
    v.valuation x = WithZero.exp (-v.ord x) := by
  rw [ord, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]

@[simp]
/- English proof (translation)
Simplify using `[ord]`. Use the proof step `@[simp]`.
-/
theorem ord_zero : v.ord 0 = 0 := by simp [ord]

@[simp]
/- English proof (translation)
Simplify using `[ord]`.
-/
theorem ord_one : v.ord 1 = 0 := by simp [ord]

/- English proof (translation)
Simplify using `only [ord, map_mul]`. Rewrite using `[WithZero.log_mul ((Valuation.ne_zero_iff v.valuation).2 hx) ((Valuation.ne_zero_iff v.valuation).2 hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v.ord (x * y) = v.ord x + v.ord y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff v.valuation).2 hx)
    ((Valuation.ne_zero_iff v.valuation).2 hy)]
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `h` using `v.ord_mul (inv_ne_zero hx) hx`. Rewrite `h` using `[inv_mul_cancel₀ hx, ord_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_inv (x : K) : v.ord x⁻¹ = -v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := v.ord_mul (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, ord_one] at h
  omega

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, v.ord_mul hx (inv_ne_zero hy), ord_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v.ord (x / y) = v.ord x - v.ord y := by
  rw [div_eq_mul_inv, v.ord_mul hx (inv_ne_zero hy), ord_inv]
  ring

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Break down `n.eq_zero_or_pos with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[hx, zero_pow hn.ne']`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hx) hx, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_pow (x : K) (n : ℕ) : v.ord (x ^ n) = n * v.ord x := by
  by_cases hx : x = 0
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp [hx, zero_pow hn.ne']
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

/- English proof (translation)
Rewrite using `[← v.valuation_le_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_nonneg_iff {x : K} (hx : x ≠ 0) : 0 ≤ v.ord x ↔ x ∈ v.ring := by
  rw [← v.valuation_le_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

/- English proof (translation)
Rewrite using `[← v.valuation_lt_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_pos_iff {x : K} (hx : x ≠ 0) : 0 < v.ord x ↔ v.ring.valuation x < 1 := by
  rw [← v.valuation_lt_one_iff, v.valuation_eq_exp_neg_ord hx, ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  omega

/- English proof (translation)
Rewrite using `[ord, v.valuation_algebraMap' hc, WithZero.log_one, neg_zero]`.
-/
theorem ord_algebraMap {c : k} (hc : c ≠ 0) : v.ord (algebraMap k K c) = 0 := by
  rw [ord, v.valuation_algebraMap' hc, WithZero.log_one, neg_zero]

/- English proof (translation)
Establish `h` using `Valuation.map_add v.valuation x y`. Rewrite `h` using `[v.valuation_eq_exp_neg_ord hx, v.valuation_eq_exp_neg_ord hy, v.valuation_eq_exp_neg_ord hxy, le_max_iff, WithZero.exp_le_exp, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem min_le_ord_add {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (v.ord x) (v.ord y) ≤ v.ord (x + y) := by
  have h := Valuation.map_add v.valuation x y
  rw [v.valuation_eq_exp_neg_ord hx, v.valuation_eq_exp_neg_ord hy,
    v.valuation_eq_exp_neg_ord hxy, le_max_iff, WithZero.exp_le_exp, WithZero.exp_le_exp] at h
  omega

/- English proof (translation)
Take `⟨π, hπ⟩` from `v.heightOneSpectrum.valuation_exists_uniformizer K`. Use `⟨π, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-WithZero.log (v.heightOneSpectrum.valuation K π) = 1`. Rewrite using `[hπ, WithZero.log_exp, neg_neg]`.
-/
theorem exists_ord_eq_one : ∃ π : K, v.ord π = 1 := by
  obtain ⟨π, hπ⟩ := v.heightOneSpectrum.valuation_exists_uniformizer K
  refine ⟨π, ?_⟩
  change -WithZero.log (v.heightOneSpectrum.valuation K π) = 1
  rw [hπ, WithZero.log_exp, neg_neg]

noncomputable def ordHom : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (v.ord x)
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul, v.ord_mul x.ne_zero y.ne_zero, ofAdd_add]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ordHom_apply (x : Kˣ) : v.ordHom x = Multiplicative.ofAdd (v.ord x) :=
  rfl

end Valuation

end Place

end Place

end GroundTheory.FunctionField
