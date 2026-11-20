import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds

namespace Formalism.GM

open Finset

namespace ArithmeticProgressionDivisibility

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[p] K) k, norm_algebraMap']`.
-/
lemma norm_int (k : ℤ) : ‖(k : K)‖ = ‖(k : ℚ_[p])‖ := by
  rw [← map_intCast (algebraMap ℚ_[p] K) k, norm_algebraMap']

omit [NormedAlgebra ℚ_[p] K] in
/- English proof (translation)
Establish `h` using `IsUltrametricDist.norm_add_le_max x (-y)`. Rewrite `h` using `[← sub_eq_add_neg, norm_neg]`. Then use the resulting hypothesis.
-/
lemma norm_sub_le_max [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [← sub_eq_add_neg, norm_neg] at h

omit [NormedAlgebra ℚ_[p] K] in
/- English proof (translation)
Assume the negation of the conclusion as `hnd`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hnd (dvd_zero _)`. Establish `hx : (k : ℚ_[p]) ≠ 0` using `by exact_mod_cast hk0`.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Take `⟨z, hz⟩ : ∃ z : ℤ, ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-z)` from `by first`. Consider the case `exact padicNormE.values_discrete hx`. Consider the case `exact ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩`. Consider the case `exact ⟨_, Padic.norm_eq_pow_val hx⟩`.

Consider the case `exact Padic.norm_values_discrete hx`. Rewrite `hk` using `[hz]`. Establish `hv : -z < 1 - (i : ℤ)` using `(zpow_lt_zpow_iff_right₀ hp1).mp hk`. Establish `hle : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ))`. Rewrite using `[hz]`.

Conclude with `zpow_le_zpow_right₀ hp1.le (by omega)`. Establish `hiff : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) ↔ (p ^ i : ℤ) ∣ k` using `by first`. Consider the case `exact padicNormE.norm_int_le_pow_iff_dvd k i`. Consider the case `exact Padic.norm_int_le_pow_iff_dvd k i`. Consider the case `(have h0 := padicNormE.norm_int_le_pow_iff_dvd (p := p) k i; push_cast at h0; exact h0)`.

Conclude with `hnd (hiff.mp hle)`.
-/
lemma dvd_of_norm_lt (k : ℤ) (i : ℕ) (hk : ‖(k : ℚ_[p])‖ < (p : ℝ) ^ (1 - (i : ℤ))) :
    (p ^ i : ℤ) ∣ k := by
  by_contra hnd
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hnd (dvd_zero _)
  have hx : (k : ℚ_[p]) ≠ 0 := by exact_mod_cast hk0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ‖(k : ℚ_[p])‖ = (p : ℝ) ^ (-z) := by
    first
      | exact padicNormE.values_discrete hx
      | exact ⟨_, Padic.norm_eq_zpow_neg_valuation hx⟩
      | exact ⟨_, Padic.norm_eq_pow_val hx⟩
      | exact Padic.norm_values_discrete hx
  rw [hz] at hk
  have hv : -z < 1 - (i : ℤ) := (zpow_lt_zpow_iff_right₀ hp1).mp hk
  have hle : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) := by
    rw [hz]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  have hiff : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) ↔ (p ^ i : ℤ) ∣ k := by
    first
      | exact padicNormE.norm_int_le_pow_iff_dvd k i
      | exact Padic.norm_int_le_pow_iff_dvd k i
      | (have h0 := padicNormE.norm_int_le_pow_iff_dvd (p := p) k i; push_cast at h0; exact h0)
  exact hnd (hiff.mp hle)

omit [NormedAlgebra ℚ_[p] K] in
/- English proof (translation)
Establish `count : ∀ (r : ℝ) (n : ℕ), min r n ≤ ∑ i ∈ Icc 1 n, (if (i : ℝ) - 1 < r then (1 : ℝ) else 0)`. Introduce `r n`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty (by omega)]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1` using `by push_cast; ring`. Distinguish the cases in `hc : ((n + 1 : ℕ) : ℝ) - 1 < r`.

Rewrite using `[if_pos hc]`. Establish `h1 : min r (n : ℝ) = n` using `min_eq_right (by linarith)`. Establish `h2` using `min_le_right r ((n + 1 : ℕ) : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hc]`.

Establish `h1 : min r (n : ℝ) = r` using `min_eq_left (by linarith)`. Establish `h2` using `min_le_left r ((n + 1 : ℕ) : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Establish `hpp : (0 : ℝ) < p` using `by linarith`.

Establish `hlogp : 0 < Real.log p` using `Real.log_pos hp1`. Take `⟨M, hM⟩ : ∃ M, M = max ‖x‖ ((p : ℝ) ^ (-(h : ℤ)))` from `⟨_, rfl⟩`. Establish `hMge : (p : ℝ) ^ (-(h : ℤ)) ≤ M` using `by rw [hM]; exact le_max_right _ _`. Establish `hxM : ‖x‖ ≤ M` using `by rw [hM]; exact le_max_left _ _`. Establish `hMpos : 0 < M` using `lt_of_lt_of_le (zpow_pos hpp _) hMge`.

Establish `hr : vmin p h x = -(Real.log M / Real.log p)` using `by rw [hM]; rfl`. Establish `hrh : vmin p h x ≤ h`. Establish `h1 : ((-(h : ℤ) : ℤ) : ℝ) * Real.log p ≤ Real.log M`. Rewrite using `[← Real.log_zpow]`. Conclude with `Real.log_le_log (zpow_pos hpp _) hMge`.

Establish `h2 : -(h : ℝ) ≤ Real.log M / Real.log p`. Rewrite using `[le_div_iff₀ hlogp]`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hr]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Distinguish the cases in `h1 : (i : ℝ) - 1 < vmin p h x`.

Establish `h2 : ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ))`. Establish `h3 : Real.log M / Real.log p < 1 - (i : ℝ)`. Rewrite `h1` using `[hr]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h3` using `[div_lt_iff₀ hlogp]`.

Establish `h4 : Real.log M < Real.log ((p : ℝ) ^ (1 - (i : ℤ)))`. Rewrite using `[Real.log_zpow]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `(Real.log_lt_log_iff hMpos (zpow_pos hpp _)).mp h4`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_pos h1, if_pos h2]`. Apply the tactic sequence `rw [if_neg h1] split_ifs <;> norm_num`.
-/
lemma vmin_le (h : ℕ) (x : K) :
    vmin p h x ≤ ∑ i ∈ Icc 1 h, (if ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) := by
  have count : ∀ (r : ℝ) (n : ℕ),
      min r n ≤ ∑ i ∈ Icc 1 n, (if (i : ℝ) - 1 < r then (1 : ℝ) else 0) := by
    intro r n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      by_cases hc : ((n + 1 : ℕ) : ℝ) - 1 < r
      · rw [if_pos hc]
        have h1 : min r (n : ℝ) = n := min_eq_right (by linarith)
        have h2 := min_le_right r ((n + 1 : ℕ) : ℝ)
        linarith
      · rw [if_neg hc]
        have h1 : min r (n : ℝ) = r := min_eq_left (by linarith)
        have h2 := min_le_left r ((n + 1 : ℕ) : ℝ)
        linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpp : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨M, hM⟩ : ∃ M, M = max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))) := ⟨_, rfl⟩
  have hMge : (p : ℝ) ^ (-(h : ℤ)) ≤ M := by rw [hM]; exact le_max_right _ _
  have hxM : ‖x‖ ≤ M := by rw [hM]; exact le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le (zpow_pos hpp _) hMge
  have hr : vmin p h x = -(Real.log M / Real.log p) := by rw [hM]; rfl
  have hrh : vmin p h x ≤ h := by
    have h1 : ((-(h : ℤ) : ℤ) : ℝ) * Real.log p ≤ Real.log M := by
      rw [← Real.log_zpow]
      exact Real.log_le_log (zpow_pos hpp _) hMge
    have h2 : -(h : ℝ) ≤ Real.log M / Real.log p := by
      rw [le_div_iff₀ hlogp]
      push_cast at h1
      linarith
    rw [hr]
    linarith
  calc vmin p h x = min (vmin p h x) (h : ℝ) := (min_eq_left hrh).symm
    _ ≤ ∑ i ∈ Icc 1 h, (if (i : ℝ) - 1 < vmin p h x then (1 : ℝ) else 0) := count _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h1 : (i : ℝ) - 1 < vmin p h x
      · have h2 : ‖x‖ < (p : ℝ) ^ (1 - (i : ℤ)) := by
          have h3 : Real.log M / Real.log p < 1 - (i : ℝ) := by
            rw [hr] at h1
            linarith
          rw [div_lt_iff₀ hlogp] at h3
          have h4 : Real.log M < Real.log ((p : ℝ) ^ (1 - (i : ℤ))) := by
            rw [Real.log_zpow]
            push_cast
            linarith
          have h5 := (Real.log_lt_log_iff hMpos (zpow_pos hpp _)).mp h4
          linarith
        rw [if_pos h1, if_pos h2]
      · rw [if_neg h1]
        split_ifs <;> norm_num

omit [NormedAlgebra ℚ_[p] K] in

/- English proof (translation)
The claim follows from `(IsCoprime.pow_left hd.symm).dvd_of_dvd_mul_left hm`.
-/
lemma dvd_cancel {d : ℤ} (hd : IsCoprime d (p : ℤ)) (i : ℕ) {m : ℤ} (hm : (p : ℤ) ^ i ∣ d * m) :
    (p : ℤ) ^ i ∣ m := (IsCoprime.pow_left hd.symm).dvd_of_dvd_mul_left hm

omit [NormedAlgebra ℚ_[p] K] in
/- English proof (translation)
Unfold `progr`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma progr_sub (t₀ d : ℤ) (a b : ℕ) : progr t₀ d a - progr t₀ d b = d * ((a : ℤ) - b) := by
  unfold progr
  ring

/- English proof (translation)
Establish `hinj : Set.InjOn (fun j => j / q) S`. Introduce `j hj j' hj' he`. Establish `h1` using `hmod j hj j' hj'`. Simplify using `only at he`. Rewrite using `[← Nat.div_add_mod j q, ← Nat.div_add_mod j' q, he, h1]`.

Establish `h2` using `Finset.card_le_card_of_injOn (fun j => j / q) (t := range (Y₀ / q + 1)) ?_ hinj`. Simplify using `using h2`. Introduce `j hj`. Establish `hj2 : j ∈ range Y₀` using `hS (Finset.mem_coe.mp hj)`. Rewrite `hj2` using `[Finset.mem_range]`.

Rewrite using `[Finset.mem_coe, Finset.mem_range]`. Use `show j / q < Y₀ / q + 1`. Establish `h3` using `Nat.div_le_div_right (c := q) hj2.le`. Use linear arithmetic over natural numbers and integers.
-/
private lemma card_le_div_add_one_of_subset_range_of_mod_eq (Y₀ q : ℕ) (hq : 0 < q) (S : Finset ℕ) (hS : S ⊆ range Y₀)
    (hmod : ∀ j ∈ S, ∀ j' ∈ S, j % q = j' % q) : S.card ≤ Y₀ / q + 1 := by
  have hinj : Set.InjOn (fun j => j / q) S := by
    intro j hj j' hj' he
    have h1 := hmod j hj j' hj'
    simp only at he
    rw [← Nat.div_add_mod j q, ← Nat.div_add_mod j' q, he, h1]
  have h2 := Finset.card_le_card_of_injOn (fun j => j / q) (t := range (Y₀ / q + 1)) ?_ hinj
  · simpa using h2
  · intro j hj
    have hj2 : j ∈ range Y₀ := hS (Finset.mem_coe.mp hj)
    rw [Finset.mem_range] at hj2
    rw [Finset.mem_coe, Finset.mem_range]
    show j / q < Y₀ / q + 1
    have h3 := Nat.div_le_div_right (c := q) hj2.le
    omega

/- English proof (translation)
Establish `hq0 : 0 < p ^ i` using `pow_pos hp.out.pos i`. Establish `hcard : ((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card ≤ Y₀ / p ^ i + 1` using `card_le_div_add_one_of_subset_range_of_mod_eq Y₀ (p ^ i) hq0 _ (Finset.filter_subset _ _) (by`. Introduce `j hj j' hj'`. Rewrite `hj`, `hj'` using `[Finset.mem_filter]`. Establish `h1 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (i : ℤ))`.

Establish `h0` using `norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)`. Rewrite `h0` using `[sub_sub_sub_cancel_right]`. Conclude with `lt_of_le_of_lt h0 (max_lt hj.2 hj'.2)`. Rewrite `h1` using `[← Int.cast_sub, progr_sub, norm_int (p := p)]`. Establish `h3` using `dvd_cancel hd i (dvd_of_norm_lt _ i h1)`.

Establish `h4 : ((p ^ i : ℕ) : ℤ) ∣ (j' : ℤ) - j`. Use `push_cast`. Rewrite using `[← dvd_neg, neg_sub]`. Conclude with `h3`. Conclude with `Nat.modEq_iff_dvd.mpr h4)`.

Establish `h5 : ((Y₀ / p ^ i : ℕ) : ℝ) ≤ (Y₀ : ℝ) / (p : ℝ) ^ i`. Establish `h6` using `Nat.cast_div_le (α := ℝ) (m := Y₀) (n := p ^ i)`. Move the coercions through the operations in `at h6`. Conclude with `h6`. Establish `h7 : ((((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℕ) : ℝ) ≤ ((Y₀ / p ^ i : ℕ) : ℝ) + 1` using `by exact_mod_cast hcard`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma card_le [IsUltrametricDist K] (ζ : K) (t₀ d : ℤ) (hd : IsCoprime d (p : ℤ)) (Y₀ i : ℕ) :
    (((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℝ)
      ≤ (Y₀ : ℝ) / (p : ℝ) ^ i + 1 := by
  have hq0 : 0 < p ^ i := pow_pos hp.out.pos i
  have hcard : ((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card
      ≤ Y₀ / p ^ i + 1 := card_le_div_add_one_of_subset_range_of_mod_eq Y₀ (p ^ i) hq0 _ (Finset.filter_subset _ _) (by
    intro j hj j' hj'
    rw [Finset.mem_filter] at hj hj'
    have h1 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (i : ℤ)) := by
      have h0 := norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)
      rw [sub_sub_sub_cancel_right] at h0
      exact lt_of_le_of_lt h0 (max_lt hj.2 hj'.2)
    rw [← Int.cast_sub, progr_sub, norm_int (p := p)] at h1
    have h3 := dvd_cancel hd i (dvd_of_norm_lt _ i h1)
    have h4 : ((p ^ i : ℕ) : ℤ) ∣ (j' : ℤ) - j := by
      push_cast
      rw [← dvd_neg, neg_sub]
      exact h3
    exact Nat.modEq_iff_dvd.mpr h4)
  have h5 : ((Y₀ / p ^ i : ℕ) : ℝ) ≤ (Y₀ : ℝ) / (p : ℝ) ^ i := by
    have h6 := Nat.cast_div_le (α := ℝ) (m := Y₀) (n := p ^ i)
    push_cast at h6
    exact h6
  have h7 : ((((range Y₀).filter (fun j : ℕ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)))).card : ℕ) : ℝ)
      ≤ ((Y₀ / p ^ i : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
  linarith

end ArithmeticProgressionDivisibility

open ArithmeticProgressionDivisibility

/- English proof (translation)
Introduce `p _ K _ _ _ ζ t₀ d Y₀ h hd`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Finset.sum_boole]`.

Conclude with `card_le ζ t₀ d hd Y₀ i`.
-/
theorem window_count_progression : WindowCountAP := by
  intro p _ K _ _ _ ζ t₀ d Y₀ h hd
  calc ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ)
      ≤ ∑ j ∈ range Y₀, ∑ i ∈ Icc 1 h,
          (if ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun j _ => vmin_le h _
    _ = ∑ i ∈ Icc 1 h, ∑ j ∈ range Y₀,
          (if ‖((progr t₀ d j : ℤ) : K) - ζ‖ < (p : ℝ) ^ (1 - (i : ℤ)) then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Finset.sum_boole]
        exact card_le ζ t₀ d hd Y₀ i

open Classical in
/- English proof (translation)
Introduce `p _ K _ _ _ roots t₀ d Y₀ h hd hY`. Establish `key : ∀ (s : Multiset K) (P : ℕ → K → Prop) [∀ j, DecidablePred (P j)] (Y : Finset ℕ), (∀ a, ∀ j ∈ Y, ∀ j' ∈ Y, P j a → P j' a → j = j') → ∑ j ∈ Y, Multiset.card (s.filter (P j)) ≤ Multiset.card s`. Introduce `s P _ Y huq`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`.

Consider the case `cons a s ih`. Establish `hstep : ∀ j ∈ Y, Multiset.card ((a ::ₘ s).filter (P j)) = Multiset.card (s.filter (P j)) + (if P j a then 1 else 0)`. Introduce `j _`. Rewrite using `[Multiset.filter_cons]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Multiset.card_cons]`. Establish `hle : ∑ j ∈ Y, (if P j a then 1 else 0) ≤ 1`. Simplify using `only [Finset.sum_boole, Nat.cast_id]`. Apply `Finset.card_le_one.mpr` to reduce the goal to its premises. Introduce `j hj j' hj'`.

Rewrite `hj`, `hj'` using `[Finset.mem_filter]`. Conclude with `huq a j hj.1 j' hj'.1 hj.2 hj'.2`. Use linear arithmetic over natural numbers and integers. Establish `hpP : p.Prime` using `Fact.out`. Establish `huniq : ∀ ζ : K, ∀ j ∈ range Y₀, ∀ j' ∈ range Y₀, ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) → ‖((progr t₀ d j' : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) → j = j'`.

Introduce `ζ j hj j' hj' h1 h2`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hpP.one_lt`. Establish `h3 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (h : ℤ))`. Establish `h0` using `norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)`. Rewrite `h0` using `[sub_sub_sub_cancel_right]`.

Establish `h4 : (p : ℝ) ^ (-(h : ℤ)) < (p : ℝ) ^ (1 - (h : ℤ))` using `zpow_lt_zpow_right₀ hp1 (by omega)`. Conclude with `lt_of_le_of_lt h0 (lt_of_le_of_lt (max_le h1 h2) h4)`. Rewrite `h3` using `[← Int.cast_sub, progr_sub, norm_int (p := p)]`. Establish `h5` using `dvd_cancel hd h (dvd_of_norm_lt _ h h3)`. Rewrite `hj`, `hj'` using `[Finset.mem_range]`.

Take `⟨c, hc⟩` from `h5`. Establish `hph : (Y₀ : ℤ) ≤ (p : ℤ) ^ h` using `by exact_mod_cast hY`. Establish `hppos : (0 : ℤ) < (p : ℤ) ^ h` using `pow_pos (by exact_mod_cast hpP.pos) h`. Establish `hc0 : c = 0`. Assume the negation of the conclusion as `hne`.

Establish `h6 : (p : ℤ) ^ h ≤ |(j : ℤ) - j'|`. Rewrite using `[hc, abs_mul, abs_of_pos hppos]`. Conclude with `le_mul_of_one_le_right hppos.le (Int.one_le_abs hne)`. Establish `h7 : |(j : ℤ) - j'| < Y₀`. Rewrite using `[abs_lt]`.

Apply the tactic sequence `constructor <;> omega`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hc` using `[hc0, mul_zero]`. Use linear arithmetic over natural numbers and integers. Use `key roots (fun j ζ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ))) (range Y₀) huniq` and compare the differences between its conclusion and the goal.
-/
theorem root_discs_disjoint_progression : DiscsDisjointAP := by
  intro p _ K _ _ _ roots t₀ d Y₀ h hd hY
  have key : ∀ (s : Multiset K) (P : ℕ → K → Prop) [∀ j, DecidablePred (P j)] (Y : Finset ℕ),
      (∀ a, ∀ j ∈ Y, ∀ j' ∈ Y, P j a → P j' a → j = j') →
      ∑ j ∈ Y, Multiset.card (s.filter (P j)) ≤ Multiset.card s := by
    intro s P _ Y huq
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      have hstep : ∀ j ∈ Y, Multiset.card ((a ::ₘ s).filter (P j))
          = Multiset.card (s.filter (P j)) + (if P j a then 1 else 0) := by
        intro j _
        rw [Multiset.filter_cons]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Multiset.card_cons]
      have hle : ∑ j ∈ Y, (if P j a then 1 else 0) ≤ 1 := by
        simp only [Finset.sum_boole, Nat.cast_id]
        apply Finset.card_le_one.mpr
        intro j hj j' hj'
        rw [Finset.mem_filter] at hj hj'
        exact huq a j hj.1 j' hj'.1 hj.2 hj'.2
      omega
  have hpP : p.Prime := Fact.out
  have huniq : ∀ ζ : K, ∀ j ∈ range Y₀, ∀ j' ∈ range Y₀,
      ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) →
      ‖((progr t₀ d j' : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) → j = j' := by
    intro ζ j hj j' hj' h1 h2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have h3 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (h : ℤ)) := by
      have h0 := norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)
      rw [sub_sub_sub_cancel_right] at h0
      have h4 : (p : ℝ) ^ (-(h : ℤ)) < (p : ℝ) ^ (1 - (h : ℤ)) := zpow_lt_zpow_right₀ hp1 (by omega)
      exact lt_of_le_of_lt h0 (lt_of_le_of_lt (max_le h1 h2) h4)
    rw [← Int.cast_sub, progr_sub, norm_int (p := p)] at h3
    have h5 := dvd_cancel hd h (dvd_of_norm_lt _ h h3)
    rw [Finset.mem_range] at hj hj'
    obtain ⟨c, hc⟩ := h5
    have hph : (Y₀ : ℤ) ≤ (p : ℤ) ^ h := by exact_mod_cast hY
    have hppos : (0 : ℤ) < (p : ℤ) ^ h := pow_pos (by exact_mod_cast hpP.pos) h
    have hc0 : c = 0 := by
      by_contra hne
      have h6 : (p : ℤ) ^ h ≤ |(j : ℤ) - j'| := by
        rw [hc, abs_mul, abs_of_pos hppos]
        exact le_mul_of_one_le_right hppos.le (Int.one_le_abs hne)
      have h7 : |(j : ℤ) - j'| < Y₀ := by
        rw [abs_lt]
        constructor <;> omega
      linarith
    rw [hc0, mul_zero] at hc
    omega
  convert key roots
    (fun j ζ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ))) (range Y₀) huniq

end Formalism.GM
