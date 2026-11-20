import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

/- English proof (translation)
Rewrite using `[v.valuation_eq_exp_neg_ord hx, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem valuation_le_exp_iff (v : Place k K) {x : K} (hx : x ≠ 0) (n : ℤ) :
    v.valuation x ≤ WithZero.exp n ↔ -n ≤ v.ord x := by
  rw [v.valuation_eq_exp_neg_ord hx, WithZero.exp_le_exp]
  omega

/- English proof (translation)
Simplify using `only [ord, Valuation.map_neg]`.
-/
theorem ord_neg (v : Place k K) (x : K) : v.ord (-x) = v.ord x := by
  simp only [ord, Valuation.map_neg]

/- English proof (translation)
Establish `hlt : v.valuation b < v.valuation a`. Rewrite using `[v.valuation_eq_exp_neg_ord ha, v.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Establish `heq : v.valuation (a + b) = v.valuation a` using `Valuation.map_add_eq_of_lt_left _ hlt`. Use `⟨fun h0 => ?_, by simp only [ord, heq]⟩` and prove the remaining obligations.

Rewrite `heq` using `[h0, map_zero]`. Conclude with `ha ((Valuation.zero_iff _).1 heq.symm)`.
-/
theorem ord_add_of_lt (v : Place k K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  have hlt : v.valuation b < v.valuation a := by
    rw [v.valuation_eq_exp_neg_ord ha, v.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]
    omega
  have heq : v.valuation (a + b) = v.valuation a := Valuation.map_add_eq_of_lt_left _ hlt
  refine ⟨fun h0 => ?_, by simp only [ord, heq]⟩
  rw [h0, map_zero] at heq
  exact ha ((Valuation.zero_iff _).1 heq.symm)

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h v.ord_zero`.
-/
theorem ne_zero_of_ord_ne_zero (v : Place k K) {x : K} (h : v.ord x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact h v.ord_zero

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Take `⟨π, hπ⟩` from `v.exists_ord_eq_one`. Conclude with `⟨π, v.ne_zero_of_ord_ne_zero (by omega), by omega, by simp⟩`. Consider the case `insert w S hwS ih`.

Rewrite `hv` using `[Finset.mem_insert, not_or]`. Take `⟨y, hy0, hyv, hyS⟩` from `ih hv.2`. Take `⟨y₁, hy₁v, hy₁w⟩` from `SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h)`. Take `⟨y₂, hy₂w, hy₂v⟩` from `SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h).symm`. Establish `hy₁0 : y₁ ≠ 0` using `fun h => hy₁w (h ▸ w.ring.zero_mem)`.

Establish `hy₂0 : y₂ ≠ 0` using `fun h => hy₂v (h ▸ v.ring.zero_mem)`. Establish `h1` using `(v.ord_nonneg_iff hy₁0).2 hy₁v`. Establish `h2 : v.ord y₂ < 0` using `not_le.1 fun h => hy₂v ((v.ord_nonneg_iff hy₂0).1 h)`. Establish `h3 : w.ord y₁ < 0` using `not_le.1 fun h => hy₁w ((w.ord_nonneg_iff hy₁0).1 h)`. Establish `h4` using `(w.ord_nonneg_iff hy₂0).2 hy₂w`.

Use `set z := y₁ / y₂ with hz`. Establish `hz0 : z ≠ 0` using `div_ne_zero hy₁0 hy₂0`. Establish `hzv : 0 < v.ord z` using `by rw [hz, v.ord_div hy₁0 hy₂0]; omega`. Establish `hzw : w.ord z < 0` using `by rw [hz, w.ord_div hy₁0 hy₂0]; omega`. Distinguish the cases in `hyw : w.ord y < 0`.

Use `⟨y, hy0, hyv, ?_⟩` and prove the remaining obligations. Introduce `w' hw'`. Rewrite `hw'` using `[Finset.mem_insert]`. Break down `hw' with rfl | hw'` into its components or cases. Conclude with `hyw`.

Conclude with `hyS w' hw'`. Use `push Not at hyw`. Use `set r : ℕ := 1 + ∑ w' ∈ S, (w'.ord y).natAbs with hr`. Establish `hzr0 : z ^ r ≠ 0` using `pow_ne_zero _ hz0`. Establish `hordr : ∀ w' : Place k K, w'.ord (z ^ r) = r * w'.ord z` using `fun w' => w'.ord_pow z r`.

Establish `hr1 : (1 : ℤ) ≤ r` using `by exact_mod_cast Nat.le_add_right 1 _`. Establish `hw` using `w.ord_add_of_lt hzr0 hy0 (by`. Rewrite using `[hordr]`. Use `mul_neg_of_pos_of_neg (show (0 : ℤ) < r by omega) hzw` as an intermediate fact. Use the proof step `omega)`.

Use `⟨z ^ r + y, hw.1, ?_, ?_⟩` and prove the remaining obligations. Use `lt_of_lt_of_le (lt_min ?_ hyv) (v.min_le_ord_add hzr0 hy0 hw.1)` and prove the remaining obligations. Rewrite using `[hordr]; exact mul_pos (by omega) hzv`. Introduce `w' hw'`. Rewrite `hw'` using `[Finset.mem_insert]`.

Break down `hw' with rfl | hw'` into its components or cases. Rewrite using `[hw.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw`. Establish `hyw'` using `hyS w' hw'`. Establish `habs : ((w'.ord y).natAbs : ℤ) < r`. Establish `h'` using `Finset.single_le_sum (f := fun w'' : Place k K => (w''.ord y).natAbs) (fun _ _ => Nat.zero_le _) hw'`.

Establish `h'' : (w'.ord y).natAbs < r` using `by rw [hr]; omega`. Conclude with `h''` after adjusting the coercions. Break down `le_or_gt 0 (w'.ord z) with hzw' | hzw'` into its components or cases. Establish `h` using `w'.ord_add_of_lt hy0 hzr0 (by`. Rewrite using `[hordr]`.

Use `mul_nonneg (show (0 : ℤ) ≤ r by omega) hzw'` as an intermediate fact. Use the proof step `omega)`. Rewrite using `[add_comm, h.2]`. Conclude with `hyw'`. Establish `h` using `w'.ord_add_of_lt hzr0 hy0 (by`.

Rewrite using `[hordr]`. Use `mul_le_mul_of_nonneg_left (show w'.ord z ≤ -1 by omega) (show (0 : ℤ) ≤ r by omega)` as an intermediate fact. Use the proof step `omega)`. Rewrite using `[h.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw'`.
-/
theorem exists_ord_pos_forall_ord_neg (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) :
    ∃ u : K, u ≠ 0 ∧ 0 < v.ord u ∧ ∀ w ∈ S, w.ord u < 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
    exact ⟨π, v.ne_zero_of_ord_ne_zero (by omega), by omega, by simp⟩
  | insert w S hwS ih =>
    rw [Finset.mem_insert, not_or] at hv
    obtain ⟨y, hy0, hyv, hyS⟩ := ih hv.2

    obtain ⟨y₁, hy₁v, hy₁w⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h)
    obtain ⟨y₂, hy₂w, hy₂v⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h).symm
    have hy₁0 : y₁ ≠ 0 := fun h => hy₁w (h ▸ w.ring.zero_mem)
    have hy₂0 : y₂ ≠ 0 := fun h => hy₂v (h ▸ v.ring.zero_mem)
    have h1 := (v.ord_nonneg_iff hy₁0).2 hy₁v
    have h2 : v.ord y₂ < 0 := not_le.1 fun h => hy₂v ((v.ord_nonneg_iff hy₂0).1 h)
    have h3 : w.ord y₁ < 0 := not_le.1 fun h => hy₁w ((w.ord_nonneg_iff hy₁0).1 h)
    have h4 := (w.ord_nonneg_iff hy₂0).2 hy₂w
    set z := y₁ / y₂ with hz
    have hz0 : z ≠ 0 := div_ne_zero hy₁0 hy₂0
    have hzv : 0 < v.ord z := by rw [hz, v.ord_div hy₁0 hy₂0]; omega
    have hzw : w.ord z < 0 := by rw [hz, w.ord_div hy₁0 hy₂0]; omega
    by_cases hyw : w.ord y < 0
    · refine ⟨y, hy0, hyv, ?_⟩
      intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · exact hyw
      · exact hyS w' hw'
    push Not at hyw
    set r : ℕ := 1 + ∑ w' ∈ S, (w'.ord y).natAbs with hr
    have hzr0 : z ^ r ≠ 0 := pow_ne_zero _ hz0
    have hordr : ∀ w' : Place k K, w'.ord (z ^ r) = r * w'.ord z := fun w' => w'.ord_pow z r
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast Nat.le_add_right 1 _
    have hw := w.ord_add_of_lt hzr0 hy0 (by
      rw [hordr]
      have := mul_neg_of_pos_of_neg (show (0 : ℤ) < r by omega) hzw
      omega)
    refine ⟨z ^ r + y, hw.1, ?_, ?_⟩
    · refine lt_of_lt_of_le (lt_min ?_ hyv) (v.min_le_ord_add hzr0 hy0 hw.1)
      rw [hordr]; exact mul_pos (by omega) hzv
    · intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · rw [hw.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw
      · have hyw' := hyS w' hw'
        have habs : ((w'.ord y).natAbs : ℤ) < r := by
          have h' := Finset.single_le_sum (f := fun w'' : Place k K => (w''.ord y).natAbs)
            (fun _ _ => Nat.zero_le _) hw'
          have h'' : (w'.ord y).natAbs < r := by rw [hr]; omega
          exact_mod_cast h''
        rcases le_or_gt 0 (w'.ord z) with hzw' | hzw'
        · have h := w'.ord_add_of_lt hy0 hzr0 (by
            rw [hordr]
            have := mul_nonneg (show (0 : ℤ) ≤ r by omega) hzw'
            omega)
          rw [add_comm, h.2]; exact hyw'
        · have h := w'.ord_add_of_lt hzr0 hy0 (by
            rw [hordr]
            have := mul_le_mul_of_nonneg_left (show w'.ord z ≤ -1 by omega)
              (show (0 : ℤ) ≤ r by omega)
            omega)
          rw [h.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw'

/- English proof (translation)
Take `⟨u, hu0, huv, huS⟩` from `v.exists_ord_pos_forall_ord_neg S hv`. Use `set s : ℕ := n.toNat + 1 with hs`. Establish `hsn : n ≤ (s : ℤ)` using `by rw [hs]; push_cast; omega`. Establish `hs1 : (1 : ℤ) ≤ s` using `by rw [hs]; push_cast; omega`. Establish `ha0 : u ^ s ≠ 0` using `pow_ne_zero _ hu0`.

Establish `hord : ∀ w : Place k K, w.ord (u ^ s) = s * w.ord u` using `fun w => w.ord_pow u s`. Establish `hv1` using `v.ord_add_of_lt one_ne_zero ha0 (by rw [hord, ord_one]; exact mul_pos (by omega) huv)`. Use `⟨(1 + u ^ s)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Establish `heq : (1 + u ^ s)⁻¹ - 1 = -(u ^ s) / (1 + u ^ s)`. Clear denominators, using `[hv1.1]` for the nonvanishing conditions.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : -(u ^ s) / (1 + u ^ s) ≠ 0` using `div_ne_zero (neg_ne_zero.2 ha0) hv1.1`. Rewrite using `[heq, v.valuation_le_exp_iff hne, v.ord_div (neg_ne_zero.2 ha0) hv1.1, ord_neg, hv1.2, ord_one, hord]`. Use `mul_le_mul_of_nonneg_left (show 1 ≤ v.ord u by omega) (show (0 : ℤ) ≤ s by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `w hw`. Establish `hw1` using `w.ord_add_of_lt ha0 one_ne_zero (by`. Rewrite using `[hord, ord_one]; exact mul_neg_of_pos_of_neg (by omega) (huS w hw))`. Rewrite `hw1` using `[add_comm]`. Rewrite using `[w.valuation_le_exp_iff (inv_ne_zero hw1.1), ord_inv, hw1.2, hord]`.

Use `mul_le_mul_of_nonneg_left (show w.ord u ≤ -1 by have := huS w hw; omega) (show (0 : ℤ) ≤ s by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_near_one (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) (n : ℤ) :
    ∃ e : K, v.valuation (e - 1) ≤ WithZero.exp (-n) ∧
      ∀ w ∈ S, w.valuation e ≤ WithZero.exp (-n) := by
  obtain ⟨u, hu0, huv, huS⟩ := v.exists_ord_pos_forall_ord_neg S hv
  set s : ℕ := n.toNat + 1 with hs
  have hsn : n ≤ (s : ℤ) := by rw [hs]; push_cast; omega
  have hs1 : (1 : ℤ) ≤ s := by rw [hs]; push_cast; omega
  have ha0 : u ^ s ≠ 0 := pow_ne_zero _ hu0
  have hord : ∀ w : Place k K, w.ord (u ^ s) = s * w.ord u := fun w => w.ord_pow u s
  have hv1 := v.ord_add_of_lt one_ne_zero ha0 (by rw [hord, ord_one]; exact mul_pos (by omega) huv)
  refine ⟨(1 + u ^ s)⁻¹, ?_, ?_⟩
  · have heq : (1 + u ^ s)⁻¹ - 1 = -(u ^ s) / (1 + u ^ s) := by
      field_simp [hv1.1]
      ring
    have hne : -(u ^ s) / (1 + u ^ s) ≠ 0 := div_ne_zero (neg_ne_zero.2 ha0) hv1.1
    rw [heq, v.valuation_le_exp_iff hne, v.ord_div (neg_ne_zero.2 ha0) hv1.1, ord_neg, hv1.2,
      ord_one, hord]
    have := mul_le_mul_of_nonneg_left (show 1 ≤ v.ord u by omega) (show (0 : ℤ) ≤ s by omega)
    omega
  · intro w hw
    have hw1 := w.ord_add_of_lt ha0 one_ne_zero (by
      rw [hord, ord_one]; exact mul_neg_of_pos_of_neg (by omega) (huS w hw))
    rw [add_comm] at hw1
    rw [w.valuation_le_exp_iff (inv_ne_zero hw1.1), ord_inv, hw1.2, hord]
    have := mul_le_mul_of_nonneg_left (show w.ord u ≤ -1 by have := huS w hw; omega)
      (show (0 : ℤ) ≤ s by omega)
    omega

/- English proof (translation)
Use `set B : ℤ := ∑ w ∈ S, ∑ v ∈ S, ((w.ord (y v)).natAbs : ℤ) with hB`. Establish `hyB : ∀ v ∈ S, ∀ w ∈ S, w.valuation (y v) ≤ WithZero.exp B`. Introduce `v hv w hw`. Distinguish the cases in `h0 : y v = 0`. Rewrite using `[h0, map_zero]`.

Conclude with `zero_le`. Rewrite using `[w.valuation_le_exp_iff h0]`. Establish `h1 : ((w.ord (y v)).natAbs : ℤ) ≤ ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ)` using `Finset.single_le_sum (f := fun v' => ((w.ord (y v')).natAbs : ℤ)) (fun _ _ => Int.natCast_nonneg _) hv`. Establish `h2 : ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) ≤ B` using `Finset.single_le_sum (f := fun w' : Place k K => ∑ v' ∈ S, ((w'.ord (y v')).natAbs : ℤ)) (fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _) hw`. Use linear arithmetic over natural numbers and integers.

Use `choose e he using fun v : Place k K => v.exists_near_one (S.erase v) (S.notMem_erase v) (n + B)`. Use `⟨∑ v ∈ S, y v * e v, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hsplit : ∑ v ∈ S, y v * e v - y w = y w * (e w - 1) + ∑ v ∈ S.erase w, y v * e v`. Rewrite using `[← Finset.add_sum_erase S _ hw]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbound : WithZero.exp B * WithZero.exp (-(n + B)) = WithZero.exp (-n)`. Rewrite using `[← WithZero.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`.

Use `Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun v hv => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, ← hbound]`. Conclude with `mul_le_mul' (hyB w hw w hw) (he w).1`. Rewrite using `[map_mul, ← hbound]`. Conclude with `mul_le_mul' (hyB v (Finset.mem_of_mem_erase hv) w hw) ((he v).2 w (Finset.mem_erase.2 ⟨fun h => (Finset.ne_of_mem_erase hv) h.symm, hw⟩))`.
-/
theorem exists_approx_const (S : Finset (Place k K)) (y : Place k K → K) (n : ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n) := by
  classical
  set B : ℤ := ∑ w ∈ S, ∑ v ∈ S, ((w.ord (y v)).natAbs : ℤ) with hB
  have hyB : ∀ v ∈ S, ∀ w ∈ S, w.valuation (y v) ≤ WithZero.exp B := by
    intro v hv w hw
    by_cases h0 : y v = 0
    · rw [h0, map_zero]; exact zero_le
    rw [w.valuation_le_exp_iff h0]
    have h1 : ((w.ord (y v)).natAbs : ℤ) ≤ ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) :=
      Finset.single_le_sum (f := fun v' => ((w.ord (y v')).natAbs : ℤ))
        (fun _ _ => Int.natCast_nonneg _) hv
    have h2 : ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) ≤ B :=
      Finset.single_le_sum (f := fun w' : Place k K => ∑ v' ∈ S, ((w'.ord (y v')).natAbs : ℤ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _) hw
    omega
  choose e he using fun v : Place k K => v.exists_near_one (S.erase v) (S.notMem_erase v) (n + B)
  refine ⟨∑ v ∈ S, y v * e v, fun w hw => ?_⟩
  have hsplit : ∑ v ∈ S, y v * e v - y w =
      y w * (e w - 1) + ∑ v ∈ S.erase w, y v * e v := by
    rw [← Finset.add_sum_erase S _ hw]
    ring
  have hbound : WithZero.exp B * WithZero.exp (-(n + B)) = WithZero.exp (-n) := by
    rw [← WithZero.exp_add]
    congr 1
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun v hv => ?_)
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB w hw w hw) (he w).1
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB v (Finset.mem_of_mem_erase hv) w hw)
      ((he v).2 w (Finset.mem_erase.2 ⟨fun h => (Finset.ne_of_mem_erase hv) h.symm, hw⟩))

/- English proof (translation)
Use `set N : ℤ := ∑ v ∈ S, ((n v).natAbs : ℤ) with hN`. Take `⟨z, hz⟩` from `exists_approx_const S y N`. Use `⟨z, fun v hv => (hz v hv).trans ?_⟩` and prove the remaining obligations. Rewrite using `[WithZero.exp_le_exp, neg_le_neg_iff]`. Use `Finset.single_le_sum (f := fun v : Place k K => ((n v).natAbs : ℤ)) (fun _ _ => Int.natCast_nonneg _) hv` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_approx (S : Finset (Place k K)) (y : Place k K → K) (n : Place k K → ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n v) := by
  set N : ℤ := ∑ v ∈ S, ((n v).natAbs : ℤ) with hN
  obtain ⟨z, hz⟩ := exists_approx_const S y N
  refine ⟨z, fun v hv => (hz v hv).trans ?_⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff]
  have := Finset.single_le_sum (f := fun v : Place k K => ((n v).natAbs : ℤ))
    (fun _ _ => Int.natCast_nonneg _) hv
  omega

end Place

end GroundTheory.FunctionField
