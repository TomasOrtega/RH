import Formalism.MahlerMeasure.QuotientUpperBoundsOfPowerBounds
import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm

namespace Formalism.GM

namespace ProgressionMeanBounds

open Finset Polynomial

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `by linarith`. Establish `hp1 : p - 1 ≠ 0` using `by linarith`. Proceed by induction on `h with`. Consider the case `zero => simp`. Consider the case `succ h ih`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma geom (p : ℝ) (hp : 2 ≤ p) (h : ℕ) :
    ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i = (1 - 1 / p ^ h) / (p - 1) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring

/- English proof (translation)
Establish `hp1 : 0 < p - 1` using `by linarith`. Establish `e : ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) = (Y₀ : ℝ) * ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i + h`. Rewrite using `[Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite using `[e, geom p hp h]`. Establish `hY : (0 : ℝ) ≤ Y₀` using `Nat.cast_nonneg _`. Establish `hq : 0 ≤ 1 / p ^ h` using `by positivity`.

Establish `: (Y₀ : ℝ) * ((1 - 1 / p ^ h) / (p - 1)) ≤ (Y₀ : ℝ) / (p - 1)`. Rewrite using `[mul_div_assoc', div_le_div_iff_of_pos_right hp1]`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sumS (p : ℝ) (hp : 2 ≤ p) (Y₀ h : ℕ) :
    ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) ≤ (Y₀ : ℝ) / (p - 1) + h := by
  have hp1 : 0 < p - 1 := by linarith
  have e : ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / p ^ i + 1) = (Y₀ : ℝ) * ∑ i ∈ Icc 1 h, (1 : ℝ) / p ^ i + h := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · simp
  rw [e, geom p hp h]
  have hY : (0 : ℝ) ≤ Y₀ := Nat.cast_nonneg _
  have hq : 0 ≤ 1 / p ^ h := by positivity
  have : (Y₀ : ℝ) * ((1 - 1 / p ^ h) / (p - 1)) ≤ (Y₀ : ℝ) / (p - 1) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hp1]
    nlinarith
  linarith

/- English proof (translation)
Proceed by induction on `roots using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih => simp [Finset.sum_add_distrib, ih]`.
-/
lemma swap {K ι : Type} (W : Finset ι) (roots : Multiset K) (f : ι → K → ℝ) :
    ∑ t ∈ W, (roots.map (f t)).sum = (roots.map (fun ζ => ∑ t ∈ W, f t ζ)).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Finset.sum_add_distrib, ih]

/- English proof (translation)
Unfold `binK`. Conclude with `(natDegree_C_mul_le _ _).trans (descPochhammer_natDegree K k).le`.
-/
theorem binK_natDegree_le (K : Type) [Field K] (k : ℕ) : (binK K k).natDegree ≤ k := by
  unfold binK
  exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree K k).le

/- English proof (translation)
Unfold `binMatK`. Apply `Polynomial.natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `k hk`. Establish `hk' : k ≤ del₀` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Conclude with `(natDegree_C_mul_le _ _).trans ((binK_natDegree_le K k).trans hk')`.
-/
theorem binMatK_entry_natDegree_le (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) (i j : Fin n) : ((binMatK K del₀ c) i j).natDegree ≤ del₀ := by
  unfold binMatK
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ del₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (natDegree_C_mul_le _ _).trans ((binK_natDegree_le K k).trans hk')

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Apply `Polynomial.natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `σ _`. Rewrite using `[Units.smul_def]`. Use `(natDegree_smul_le _ _).trans ?_` and prove the remaining obligations.

Use `(natDegree_prod_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem binMatK_det_natDegree_le (K : Type) [Field K] {n : ℕ} (del₀ : ℕ)
    (c : Fin n → Fin n → ℕ → K) : ((binMatK K del₀ c).det).natDegree ≤ del₀ * n := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, ((binMatK K del₀ c) (σ i) i).natDegree ≤ ∑ _i : Fin n, del₀ :=
        Finset.sum_le_sum (fun i _ => binMatK_entry_natDegree_le K del₀ c (σ i) i)
    _ = del₀ * n := by simp [mul_comm]

end ProgressionMeanBounds

open Finset Polynomial ProgressionMeanBounds

/- English proof (translation)
Introduce `p _ K _ _ _ roots lam La₀ E n₀ del₀ t₀ d Y₀ h β hd hY hYp hE hcard hlam hj`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).two_le`. Establish `hY0 : (0 : ℝ) < Y₀` using `by exact_mod_cast hY`. Establish `hsum : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤ ∑ j ∈ range Y₀, ((lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) + E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ))`. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_le_sum hj`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul, ← Finset.mul_sum, swap (range Y₀) roots (fun j ζ => vmin p h ((progr t₀ d j : K) - ζ))]`. Establish `hV : (roots.map (fun ζ => ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ))).sum ≤ (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1) + h)`. Combine the equalities or inequalities in the displayed calculation. Establish `hDD : (∑ j ∈ range Y₀, ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤ (roots.card : ℝ)`.

Use `hD p K roots t₀ d Y₀ h hd hYp` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hNc : (roots.card : ℝ) ≤ (del₀ : ℝ) * n₀` using `by exact_mod_cast hcard`. Establish `hN0 : (0 : ℝ) ≤ roots.card` using `Nat.cast_nonneg _`. Establish `hh0 : (0 : ℝ) ≤ h` using `Nat.cast_nonneg _`.

Establish `h1 : (Y₀ : ℝ) * lam + (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1)) = (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1))` using `by ring`. Establish `h2 : (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) ≤ (Y₀ : ℝ) * ((n₀ : ℝ) * La₀)` using `mul_le_mul_of_nonneg_left hlam hY0.le`. Establish `h3 : (roots.card : ℝ) * h ≤ (del₀ : ℝ) * n₀ * h` using `mul_le_mul_of_nonneg_right hNc hh0`. Establish `h4 : E * (roots.card : ℝ) ≤ E * ((del₀ : ℝ) * n₀)` using `mul_le_mul_of_nonneg_left hNc hE.le`. Establish `h5 : E * (∑ j ∈ range Y₀, ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤ E * (roots.card : ℝ)` using `mul_le_mul_of_nonneg_left hDD hE.le`.

Establish `hS : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤ (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀)`. Use the polynomial consequences of the given equalities and inequalities. Establish `eR : (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E) * Y₀ * E = (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[div_le_iff₀ hY0, ← mul_le_mul_iff_of_pos_right hE, eR]`. Conclude with `hS`.
-/
theorem windowMeanAP_of (hC : WindowCountAP) (hD : DiscsDisjointAP) : WindowMeanAP := by
  intro p _ K _ _ _ roots lam La₀ E n₀ del₀ t₀ d Y₀ h β hd hY hYp hE hcard hlam hj
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hY0 : (0 : ℝ) < Y₀ := by exact_mod_cast hY
  have hsum : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      ∑ j ∈ range Y₀, ((lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hj
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    ← Finset.mul_sum, swap (range Y₀) roots (fun j ζ => vmin p h ((progr t₀ d j : K) - ζ))] at hsum
  have hV : (roots.map (fun ζ => ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ))).sum ≤
      (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1) + h) := by
    calc _ ≤ (roots.map (fun _ => (Y₀ : ℝ) / ((p : ℝ) - 1) + h)).sum :=
          Multiset.sum_map_le_sum_map _ _
            (fun ζ _ => (hC p K ζ t₀ d Y₀ h hd).trans (sumS p hp2 Y₀ h))
      _ = _ := by rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  have hDD : (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      (roots.card : ℝ) := by
    have := hD p K roots t₀ d Y₀ h hd hYp
    exact_mod_cast this
  have hNc : (roots.card : ℝ) ≤ (del₀ : ℝ) * n₀ := by exact_mod_cast hcard
  have hN0 : (0 : ℝ) ≤ roots.card := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have h1 : (Y₀ : ℝ) * lam + (roots.card : ℝ) * ((Y₀ : ℝ) / ((p : ℝ) - 1)) =
      (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) := by ring
  have h2 : (Y₀ : ℝ) * (lam + (roots.card : ℝ) / ((p : ℝ) - 1)) ≤ (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) :=
    mul_le_mul_of_nonneg_left hlam hY0.le
  have h3 : (roots.card : ℝ) * h ≤ (del₀ : ℝ) * n₀ * h := mul_le_mul_of_nonneg_right hNc hh0
  have h4 : E * (roots.card : ℝ) ≤ E * ((del₀ : ℝ) * n₀) := mul_le_mul_of_nonneg_left hNc hE.le
  have h5 : E * (∑ j ∈ range Y₀,
      ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) ≤
      E * (roots.card : ℝ) := mul_le_mul_of_nonneg_left hDD hE.le
  have hS : (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) * E ≤
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    nlinarith
  have eR : (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E) * Y₀ * E =
      (Y₀ : ℝ) * ((n₀ : ℝ) * La₀) + (del₀ : ℝ) * n₀ * h + E * ((del₀ : ℝ) * n₀) := by
    field_simp
    ring
  rw [div_le_iff₀ hY0, ← mul_le_mul_iff_of_pos_right hE, eR]
  exact hS

/- English proof (translation)
Introduce `p _ K _ _ _ n del₀ h E c lead roots t₀ d Y₀ La₀ U V dg hd hY hYp hdel hE hlead hc hdet hj hlam`. Establish `hcard : roots.card ≤ del₀ * n`. Establish `e : ((binMatK K del₀ c).det).natDegree = roots.card`. Rewrite using `[hdet, natDegree_C_mul hlead, natDegree_multiset_prod_X_sub_C_eq_card]`. Rewrite using `[← e]`.

Conclude with `binMatK_det_natDegree_le K del₀ c`. Use `hW p K roots (-Real.logb p ‖lead‖) La₀ E n del₀ t₀ d Y₀ h (fun t => (univ.filter (fun i => ‖dg t i‖ ≤ (p : ℝ) ^ (-E))).card) hd hY hYp hE hcard hlam ?_` and prove the remaining obligations. Introduce `j hjr`. Take `⟨hU, hV, hdU, hdV, hmap⟩` from `hj j hjr`. Conclude with `hL p K n del₀ h E c lead roots (progr t₀ d j) (U (progr t₀ d j)) (V (progr t₀ d j)) (dg (progr t₀ d j)) hc hU hV hdU hdV hE.le hdel hlead hdet hmap`.
-/
theorem windowFullAP_of (hL : ValuationWindowLowerBound) (hW : WindowMeanAP) : WindowFullAP := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ d Y₀ La₀ U V dg hd hY hYp hdel hE hlead hc hdet hj hlam
  have hcard : roots.card ≤ del₀ * n := by
    have e : ((binMatK K del₀ c).det).natDegree = roots.card := by
      rw [hdet, natDegree_C_mul hlead, natDegree_multiset_prod_X_sub_C_eq_card]
    rw [← e]
    exact binMatK_det_natDegree_le K del₀ c
  refine hW p K roots (-Real.logb p ‖lead‖) La₀ E n del₀ t₀ d Y₀ h
    (fun t => (univ.filter (fun i => ‖dg t i‖ ≤ (p : ℝ) ^ (-E))).card) hd hY hYp hE hcard hlam ?_
  intro j hjr
  obtain ⟨hU, hV, hdU, hdV, hmap⟩ := hj j hjr
  exact hL p K n del₀ h E c lead roots (progr t₀ d j) (U (progr t₀ d j)) (V (progr t₀ d j))
    (dg (progr t₀ d j)) hc hU hV hdU hdV hE.le hdel hlead hdet hmap

end Formalism.GM
