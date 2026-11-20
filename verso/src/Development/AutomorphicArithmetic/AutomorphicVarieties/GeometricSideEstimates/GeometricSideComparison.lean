import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt

open UpperTheory.V.Lit.Geo

set_option maxHeartbeats 800000 in
/- English proof (translation)
Unfold `MeanLow`. Use `⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩` and prove the remaining obligations. Introduce `A V _ _ _ φ hinj hS hT h2`. Use `haveI : IsAddTorsionFree V := by`. Prove the components needed by the constructor for the conclusion.

Introduce `n hn x y hxy`. Simplify using `only at hxy`. Establish `h : ((n : ℝ)) • x = ((n : ℝ)) • y` using `by simpa [Nat.cast_smul_eq_nsmul] using hxy`. Conclude with `smul_right_injective V (Nat.cast_ne_zero.mpr hn) h`. Establish `hfin : {x : A | ‖φ x‖ < 1}.Finite`.

Establish `h` using `hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))`. Rewrite `h` using `[Filter.eventually_cofinite]`. Use `h.subset ?_` and prove the remaining obligations. Introduce `x (hx : ‖φ x‖ < 1)`. Simplify using `only [Set.mem_setOf_eq, not_lt]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `ha2 : ‖φ x‖ ^ 2 ≤ 1` using `by nlinarith [norm_nonneg (φ x)]`. Use polynomial arithmetic with `[Real.pi_pos]`. Establish `hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite` using `hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)`. Use `set H := hfin.toFinset with hH`.

Use `set F := hfin2.toFinset with hF`. Establish `hFH : F ⊆ H`. Introduce `x hx`. Simplify using `only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcd : 2 * F.card - 1 ≤ H.card`. Establish `h0 : (0 : A) ∈ F`. Simplify using `only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]`. Evaluate the numerical expressions. Establish `hne : (F.image φ).Nonempty` using `⟨φ 0, Finset.mem_image_of_mem _ h0⟩`.

Establish `hcdv` using `cauchy_davenport_of_isAddTorsionFree hne hne`. Establish `hcard : (F.image φ).card = F.card` using `Finset.card_image_of_injective _ hinj`. Use `open scoped Pointwise in`. Establish `hsub : F.image φ + F.image φ ⊆ H.image φ`. Introduce `v hv`.

Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.mp hv`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp ha`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.mp hb`. Use `Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩` and prove the remaining obligations. Simplify using `only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢`.

Rewrite using `[map_add]`. Combine the equalities or inequalities in the displayed calculation. Establish `hle` using `Finset.card_le_card hsub`. Rewrite `hle` using `[Finset.card_image_of_injective _ hinj]`. Rewrite `hcdv` using `[hcard]`.

Use linear arithmetic over natural numbers and integers. Establish `hsd` using `Finset.card_sdiff_add_card_eq_card hFH`. Establish `hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1`. Establish `: F.card ≤ (H \ F).card + 1` using `by omega`. Conclude with `this` after adjusting the coercions.

Establish `hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)`. Use `le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))` and prove the remaining obligations. Establish `hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)`. Introduce `x hx`. Simplify using `only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx`.

Take `⟨h1, h3⟩` from `hx`. Establish `ha2 : ‖φ x‖ ^ 2 ≤ 1` using `by nlinarith [norm_nonneg (φ x)]`. Establish `e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2)` using `Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])`. Establish `e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2` using `by nlinarith`. Use `Real.exp_pos (-Real.pi)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ _ := Finset.sum_le_sum hpt`. Establish `hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card`.

Establish `hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0)` using `summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)`. Establish `hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card`. Rewrite using `[tsum_eq_sum (s := F) (fun x hx => if_neg hx)]`. Simplify using the standard rewrite rules. Establish `hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)`.

Introduce `x`. Establish `hp` using `Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)`. Distinguish the cases in `hx : x ∈ F`. Rewrite using `[if_pos hx]`. Establish `: Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1` using `Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])`.

Use polynomial arithmetic with `[sq_nonneg ‖φ x‖]`. Rewrite using `[if_neg hx]`. Simplify using `only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx`. Establish `: (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Establish `hE` using `Real.exp_pos (-Real.pi)`. Establish `hE1 : Real.exp (-Real.pi) ≤ 1` using `Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])`. Establish `hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)` using `tsum_nonneg (fun x => by positivity)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le, mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]`.
-/
theorem UpperTheory.geometric_side_comparison :
    MeanLow := by
  unfold MeanLow
  refine ⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩
  intro A V _ _ _ φ hinj hS hT h2
  classical
  haveI : IsAddTorsionFree V := by
    constructor
    intro n hn x y hxy
    simp only at hxy
    have h : ((n : ℝ)) • x = ((n : ℝ)) • y := by simpa [Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  have hfin : {x : A | ‖φ x‖ < 1}.Finite := by
    have h := hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro x (hx : ‖φ x‖ < 1)
    simp only [Set.mem_setOf_eq, not_lt]
    apply Real.exp_le_exp.mpr
    have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
    nlinarith [Real.pi_pos]
  have hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite :=
    hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)
  set H := hfin.toFinset with hH
  set F := hfin2.toFinset with hF
  have hFH : F ⊆ H := by
    intro x hx
    simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcd : 2 * F.card - 1 ≤ H.card := by
    have h0 : (0 : A) ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
      norm_num
    have hne : (F.image φ).Nonempty := ⟨φ 0, Finset.mem_image_of_mem _ h0⟩
    have hcdv := cauchy_davenport_of_isAddTorsionFree hne hne
    have hcard : (F.image φ).card = F.card := Finset.card_image_of_injective _ hinj
    open scoped Pointwise in
    have hsub : F.image φ + F.image φ ⊆ H.image φ := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩
      simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add]
      calc ‖φ x + φ y‖ ≤ ‖φ x‖ + ‖φ y‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hle
    rw [hcard] at hcdv
    omega
  have hsd := Finset.card_sdiff_add_card_eq_card hFH
  have hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1 := by
    have : F.card ≤ (H \ F).card + 1 := by omega
    exact_mod_cast this
  have hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤
      ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    refine le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))
    have hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
      intro x hx
      simp only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
      obtain ⟨h1, h3⟩ := hx
      have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
      have e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
      have := Real.exp_pos (-Real.pi)
      nlinarith
    calc ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) = ∑ x ∈ H \ F, Real.exp (-Real.pi) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card := by
    have hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)
    have hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card := by
      rw [tsum_eq_sum (s := F) (fun x hx => if_neg hx)]
      simp
    have hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
        4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0) := by
      intro x
      have hp := Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)
      by_cases hx : x ∈ F
      · rw [if_pos hx]
        have : Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])
        nlinarith [sq_nonneg ‖φ x‖]
      · rw [if_neg hx]
        simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
        have : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
        nlinarith
    calc _ ≤ ∑' x, (4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)) :=
          Summable.tsum_le_tsum hle hS ((hT.mul_left 4).add hg)
      _ = _ := by rw [Summable.tsum_add (hT.mul_left 4) hg, tsum_mul_left, hsum]
  have hE := Real.exp_pos (-Real.pi)
  have hE1 : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    tsum_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le,
    mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]
