import Mathlib

open Complex Filter Topology

namespace GlobalTheory.RealZeros

/- English proof (translation)
Establish `hs0 : -s ≠ 0`. Introduce `h`. Establish `: s = 0` using `neg_eq_zero.mp h`. Simplify using `[this] at hs`. Establish `key` using `norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x : ℝ => (x : ℂ) ^ (-s)) (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) (a := a) (b := b) (C := ‖s‖ * a ^ (-s.re - 1)) (fun x hx => (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha hx.1)) hs0).hasDerivWithinAt) (fun …`.

Establish `hx0 : 0 < x` using `lt_of_lt_of_le ha hx.1`. Rewrite using `[norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `: (-s - 1).re = -s.re - 1` using `by simp`. Rewrite using `[this]`.

Conclude with `Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith))`. Use `b ⟨hab, le_rfl⟩`. Rewrite `key` using `[norm_sub_rev]`. Then use the resulting hypothesis.
-/
theorem norm_cpow_sub_le {s : ℂ} (hs : 0 < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    simp [this] at hs
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x : ℝ => (x : ℂ) ^ (-s))
    (f' := fun x : ℝ => (-s) * (x : ℂ) ^ (-s - 1)) (a := a) (b := b)
    (C := ‖s‖ * a ^ (-s.re - 1))
    (fun x hx => (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha hx.1)) hs0).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have : (-s - 1).re = -s.re - 1 := by simp
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith))
    b ⟨hab, le_rfl⟩
  rwa [norm_sub_rev] at key

noncomputable def br (N c d k : ℕ) (s : ℂ) : ℂ :=
  ((N * k + c : ℕ) : ℂ) ^ (-s) - ((N * k + d : ℕ) : ℂ) ^ (-s)

/- English proof (translation)
Establish `h1 : k + 1 ≤ N * k + c` using `by nlinarith`. Establish `h1' : ((k + 1 : ℕ) : ℝ) ≤ ((N * k + c : ℕ) : ℝ)` using `by exact_mod_cast h1`. Establish `h0 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.le_add_left 1 k`. Establish `key` using `norm_cpow_sub_le (s := s) (by linarith) (a := ((N * k + c : ℕ) : ℝ)) (b := ((N * k + d : ℕ) : ℝ)) (by linarith) (by exact_mod_cast Nat.add_le_add_left hcd _)`. Simplify using `only [ofReal_natCast] at key`.

Use `key.trans ?_` and prove the remaining obligations. Establish `h2 : ((N * k + c : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (-ε - 1)` using `(Real.rpow_le_rpow_of_nonpos (by linarith) h1' (by linarith)).trans (Real.rpow_le_rpow_of_exponent_le h0 (by linarith))`. Establish `h3 : ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ) ≤ d`. Use `push_cast`. Establish `: (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (0 : ℝ) ≤ ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ)`. Establish `: ((N * k + c : ℕ) : ℝ) ≤ ((N * k + d : ℕ) : ℝ)`. Conclude with `Nat.add_le_add_left hcd _` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hR0 : 0 ≤ R` using `(norm_nonneg _).trans hR.le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_br_le {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) (k : ℕ) {s : ℂ} {ε R : ℝ}
    (hε : 0 < ε) (hs : ε < s.re) (hR : ‖s‖ < R) :
    ‖br N c d k s‖ ≤ R * d * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) := by
  have h1 : k + 1 ≤ N * k + c := by nlinarith
  have h1' : ((k + 1 : ℕ) : ℝ) ≤ ((N * k + c : ℕ) : ℝ) := by exact_mod_cast h1
  have h0 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have key := norm_cpow_sub_le (s := s) (by linarith) (a := ((N * k + c : ℕ) : ℝ))
    (b := ((N * k + d : ℕ) : ℝ)) (by linarith) (by exact_mod_cast Nat.add_le_add_left hcd _)
  simp only [ofReal_natCast] at key
  refine key.trans ?_
  have h2 : ((N * k + c : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
    (Real.rpow_le_rpow_of_nonpos (by linarith) h1' (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le h0 (by linarith))
  have h3 : ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ) ≤ d := by
    push_cast
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    linarith
  have h4 : (0 : ℝ) ≤ ((N * k + d : ℕ) : ℝ) - ((N * k + c : ℕ) : ℝ) := by
    have : ((N * k + c : ℕ) : ℝ) ≤ ((N * k + d : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_left hcd _
    linarith
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR.le
  calc _ ≤ R * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) * d := by gcongr
    _ = _ := by ring

/- English proof (translation)
The claim follows from `((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-ε - 1)) 1).mpr (Real.summable_nat_rpow.mpr (by linarith))).mul_left C`.
-/
theorem summable_bound {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Summable fun k : ℕ => C * ((k + 1 : ℕ) : ℝ) ^ (-ε - 1) :=
  ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-ε - 1)) 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith))).mul_left C

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded (summable_bound (half_pos hs) ((‖s‖ + 1) * d)) (fun k => norm_br_le hN hc hcd k (half_pos hs) (half_lt_self hs) (lt_add_one _))`.
-/
theorem summable_br {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) {s : ℂ}
    (hs : 0 < s.re) : Summable fun k => br N c d k s :=
  Summable.of_norm_bounded (summable_bound (half_pos hs) ((‖s‖ + 1) * d))
    (fun k => norm_br_le hN hc hcd k (half_pos hs) (half_lt_self hs) (lt_add_one _))

/- English proof (translation)
Introduce `s hs`. Establish `hs' : 0 < s.re` using `hs`. Establish `hU : IsOpen {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1}` using `(isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)`. Establish `hd : DifferentiableOn ℂ (fun z => ∑' k, br N c d k z) {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1}`. Use `differentiableOn_tsum_of_summable_norm (summable_bound (half_pos hs') ((‖s‖ + 1) * d)) (fun k => ?_) hU (fun k z hz => norm_br_le hN hc hcd k (half_pos hs') hz.1 hz.2)` and prove the remaining obligations.

Introduce `z _`. Establish `h1 : ((N * k + c : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `h2 : ((N * k + d : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Conclude with `((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub (differentiableAt_id.neg.const_cpow (Or.inl h2))).differentiableWithinAt`. Conclude with `(hd.differentiableAt (hU.mem_nhds ⟨half_lt_self hs', lt_add_one _⟩)).differentiableWithinAt`.
-/
theorem differentiableOn_tsum_br {N c d : ℕ} (hN : 1 ≤ N) (hc : 1 ≤ c) (hcd : c ≤ d) :
    DifferentiableOn ℂ (fun s => ∑' k, br N c d k s) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hU : IsOpen {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hd : DifferentiableOn ℂ (fun z => ∑' k, br N c d k z)
      {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1} := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_bound (half_pos hs') ((‖s‖ + 1) * d)) (fun k => ?_) hU
      (fun k z hz => norm_br_le hN hc hcd k (half_pos hs') hz.1 hz.2)
    intro z _
    have h1 : ((N * k + c : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((N * k + d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl h2))).differentiableWithinAt
  exact (hd.differentiableAt (hU.mem_nhds ⟨half_lt_self hs', lt_add_one _⟩)).differentiableWithinAt

/- English proof (translation)
Establish `h1` using `(Nat.divModEquiv N).symm.hasSum_iff.mpr h`. Use `h1.prod_fiberwise (fun k => ?_)` and prove the remaining obligations. Use `hasSum_fintype (fun j : Fin N => f (N * k + j))` as an intermediate fact. Simplify `this` using `[mul_comm]`.
-/
theorem hasSum_group {f : ℕ → ℂ} {a : ℂ} (N : ℕ) [NeZero N] (h : HasSum f a) :
    HasSum (fun k => ∑ j : Fin N, f (N * k + j)) a := by
  have h1 := (Nat.divModEquiv N).symm.hasSum_iff.mpr h
  refine h1.prod_fiberwise (fun k => ?_)
  have := hasSum_fintype (fun j : Fin N => f (N * k + j))
  simpa [mul_comm] using this

/- English proof (translation)
Rewrite using `[br, ofReal_sub, ofReal_cpow (Nat.cast_nonneg _), ofReal_cpow (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem br_ofReal (N c d k : ℕ) (σ : ℝ) :
    br N c d k σ = ((((N * k + c : ℕ) : ℝ) ^ (-σ) - ((N * k + d : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [br, ofReal_sub, ofReal_cpow (Nat.cast_nonneg _), ofReal_cpow (Nat.cast_nonneg _)]
  simp

/- English proof (translation)
The claim follows from `convex_halfSpace_re_gt 0`.
-/
theorem convex_re_pos : Convex ℝ {s : ℂ | 0 < s.re} := convex_halfSpace_re_gt 0

/- English proof (translation)
Establish `h0 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s)`. Establish `hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)`. Use `(summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)` as an intermediate fact. Simplify using `using this`. Rewrite using `[zeta_eq_tsum_one_div_nat_add_one_cpow hs]`.

Simplify `hsum.hasSum` using `[cpow_neg]`. Establish `h1` using `hasSum_group 2 h0`. Establish `h2` using `h0.mul_left (2 * (2 : ℂ) ^ (-s))`. Establish `h3` using `h1.sub h2`. Rewrite using `[sub_mul, one_mul, ← h3.tsum_eq]`.

Use `tsum_congr fun k => ?_` and prove the remaining obligations. Establish `: ((2 * k + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((k + 1 : ℕ) : ℂ) ^ (-s)`. Use `natCast_mul_natCast_cpow 2 (k + 1) (-s)` as an intermediate fact. Rewrite using `[show 2 * k + 2 = 2 * (k + 1) by ring, Nat.cast_mul, this]`. Simplify using the standard rewrite rules.

Simplify using `only [Fin.sum_univ_two, br, Fin.val_zero, Fin.val_one, add_zero, add_assoc]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s = ∑' k, br 2 1 2 k s := by
  have h0 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
    have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr
        (Complex.summable_one_div_nat_cpow.mpr hs)
      simpa using this
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    simpa [cpow_neg] using hsum.hasSum
  have h1 := hasSum_group 2 h0
  have h2 := h0.mul_left (2 * (2 : ℂ) ^ (-s))
  have h3 := h1.sub h2
  rw [sub_mul, one_mul, ← h3.tsum_eq]
  refine tsum_congr fun k => ?_
  have : ((2 * k + 2 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((k + 1 : ℕ) : ℂ) ^ (-s) := by
    have := natCast_mul_natCast_cpow 2 (k + 1) (-s)
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, Nat.cast_mul, this]
    simp
  simp only [Fin.sum_univ_two, br, Fin.val_zero, Fin.val_one, add_zero, add_assoc]
  rw [this]
  ring

/- English proof (translation)
Establish `hF : ∀ U : Set ℂ, IsOpen U → (1 : ℂ) ∉ U → AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) U`. Introduce `U hU h1`. Use `DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU` and prove the remaining obligations. Establish `hz1 : z ≠ 1` using `fun h => h1 (h ▸ hz)`. Conclude with `(((differentiableAt_const _).sub ((differentiableAt_id.neg.const_cpow (Or.inl two_ne_zero)).const_mul _)).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt`.

Establish `hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 2 1 2 k s) {s | 0 < s.re}` using `(differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).analyticOnNhd (isOpen_lt continuous_const continuous_re)`. Establish `hAo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im})` using `(isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)`. Establish `hBo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})` using `(isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)`. Establish `hA` using `(hF _ hAo (by simp)).eqOn_of_preconnected_of_eventuallyEq (hG.mono Set.inter_subset_left) (convex_re_pos.inter (convex_halfSpace_im_gt 0)).isPreconnected (z₀ := 2 + I) (by simp) (by filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (1 : ℝ) < (2 + I : ℂ).re …`. Establish `hB` using `(hF _ hBo (by simp)).eqOn_of_preconnected_of_eventuallyEq (hG.mono Set.inter_subset_left) (convex_re_pos.inter (convex_halfSpace_re_lt 1)).isPreconnected (z₀ := 2⁻¹ + I) (by norm_num) (by filter_upwards [hAo.mem_nhds (show (2⁻¹ + I : ℂ) ∈ _ by norm_num)] with z hz using hA hz)`.

Conclude with `hB ⟨hs, hs1⟩`.
-/
theorem eta_eq_of_strip {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s = ∑' k, br 2 1 2 k s := by
  have hF : ∀ U : Set ℂ, IsOpen U → (1 : ℂ) ∉ U →
      AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) U := by
    intro U hU h1
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz1 : z ≠ 1 := fun h => h1 (h ▸ hz)
    exact (((differentiableAt_const _).sub ((differentiableAt_id.neg.const_cpow
      (Or.inl two_ne_zero)).const_mul _)).mul
      (differentiableAt_riemannZeta hz1)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 2 1 2 k s) {s | 0 < s.re} :=
    (differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).analyticOnNhd
      (isOpen_lt continuous_const continuous_re)
  have hAo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
  have hBo : IsOpen ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}) :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hA := (hF _ hAo (by simp)).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono Set.inter_subset_left)
    (convex_re_pos.inter (convex_halfSpace_im_gt 0)).isPreconnected (z₀ := 2 + I) (by simp)
    (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz using eta_eq_of_one_lt hz)
  have hB := (hF _ hBo (by simp)).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono Set.inter_subset_left)
    (convex_re_pos.inter (convex_halfSpace_re_lt 1)).isPreconnected (z₀ := 2⁻¹ + I)
    (by norm_num)
    (by
      filter_upwards [hAo.mem_nhds (show (2⁻¹ + I : ℂ) ∈ _ by norm_num)] with z hz using hA hz)
  exact hB ⟨hs, hs1⟩

/- English proof (translation)
Introduce `h`. Establish `key` using `eta_eq_of_strip (s := σ) (by simpa using h0) (by simpa using h1)`. Establish `hsum` using `summable_br (N := 2) (c := 1) (d := 2) (by norm_num) le_rfl (by norm_num) (s := σ) (by simpa using h0)`. Simplify using `only [br_ofReal] at key hsum`. Rewrite `key` using `[h, mul_zero, ← ofReal_tsum]`.

Rewrite `hsum` using `[summable_ofReal]`. Establish `hpos : ∀ k : ℕ, 0 < ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ)` using `fun k => sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by positivity) (by exact_mod_cast Nat.lt_succ_self _) (by linarith))`. Use `hsum.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)` as an intermediate fact. Conclude with `this.ne (by exact_mod_cast key)`.
-/
theorem riemannZeta_ne_zero_of_mem_Ioo (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  intro h
  have key := eta_eq_of_strip (s := σ) (by simpa using h0) (by simpa using h1)
  have hsum := summable_br (N := 2) (c := 1) (d := 2) (by norm_num) le_rfl (by norm_num)
    (s := σ) (by simpa using h0)
  simp only [br_ofReal] at key hsum
  rw [h, mul_zero, ← ofReal_tsum] at key
  rw [summable_ofReal] at hsum
  have hpos : ∀ k : ℕ, 0 < ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) :=
    fun k => sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by positivity)
      (by exact_mod_cast Nat.lt_succ_self _) (by linarith))
  have := hsum.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  exact this.ne (by exact_mod_cast key)

/- English proof (translation)
Establish `hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ)) (-σ * x ^ (-σ - 1) - 1 * -σ * (x + 2) ^ (-σ - 1)) x` using `fun x hx => (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).sub (((hasDerivAt_id x).add_const 2).rpow_const (Or.inl (by simp only [id]; linarith)))`. Use `strictAntiOn_of_deriv_neg (convex_Ioi 0) (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[interior_Ioi]`. Establish `hx' : 0 < x` using `hx`. Rewrite using `[(hd x hx').deriv]`.

Establish `: (x + 2) ^ (-σ - 1) < x ^ (-σ - 1)` using `Real.rpow_lt_rpow_of_neg hx' (by linarith) (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem strictAntiOn_diff {σ : ℝ} (h0 : 0 < σ) :
    StrictAntiOn (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ)) (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ))
      (-σ * x ^ (-σ - 1) - 1 * -σ * (x + 2) ^ (-σ - 1)) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).sub
      (((hasDerivAt_id x).add_const 2).rpow_const (Or.inl (by simp only [id]; linarith)))
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
  rw [interior_Ioi] at hx
  have hx' : 0 < x := hx
  rw [(hd x hx').deriv]
  have : (x + 2) ^ (-σ - 1) < x ^ (-σ - 1) :=
    Real.rpow_lt_rpow_of_neg hx' (by linarith) (by linarith)
  nlinarith

/- English proof (translation)
Establish `hs0 : 0 < s.re` using `by linarith`. Rewrite using `[DirichletCharacter.LFunction_eq_LSeries χ hs, ← (summable_br (by norm_num) le_rfl (by norm_num) hs0).tsum_sub (summable_br (by norm_num) (by norm_num) (by norm_num) hs0)]`. Establish `h0 : HasSum (LSeries.term (fun n : ℕ => χ n) s) (LSeries (fun n : ℕ => χ n) s)` using `(DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum`. Rewrite using `[← (hasSum_group 8 h0).tsum_eq]`. Use `tsum_congr fun k => ?_` and prove the remaining obligations.

Establish `ht : ∀ j : ℕ, LSeries.term (fun n : ℕ => χ n) s (8 * k + j) = ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) * ((8 * k + j : ℕ) : ℂ) ^ (-s)`. Introduce `j`. Establish `hc : ((8 * k + j : ℕ) : ZMod 8) = (j : ZMod 8)`. Rewrite using `[Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]`. Rewrite using `[LSeries.term_def₀ (by rw [Nat.cast_zero, hχ]; simp), hc, hχ]`.

Simplify using `only [ht, Fin.sum_univ_eight, br]`. Establish `e0 : ZMod.χ₈ (((0 : Fin 8) : ℕ) : ZMod 8) = 0` using `by decide`. Establish `e1 : ZMod.χ₈ (((1 : Fin 8) : ℕ) : ZMod 8) = 1` using `by decide`. Establish `e2 : ZMod.χ₈ (((2 : Fin 8) : ℕ) : ZMod 8) = 0` using `by decide`. Establish `e3 : ZMod.χ₈ (((3 : Fin 8) : ℕ) : ZMod 8) = -1` using `by decide`.

Establish `e4 : ZMod.χ₈ (((4 : Fin 8) : ℕ) : ZMod 8) = 0` using `by decide`. Establish `e5 : ZMod.χ₈ (((5 : Fin 8) : ℕ) : ZMod 8) = -1` using `by decide`. Establish `e6 : ZMod.χ₈ (((6 : Fin 8) : ℕ) : ZMod 8) = 0` using `by decide`. Establish `e7 : ZMod.χ₈ (((7 : Fin 8) : ℕ) : ZMod 8) = 1` using `by decide`. Rewrite using `[e0, e1, e2, e3, e4, e5, e6, e7]`.

Establish `f1 : ((1 : Fin 8) : ℕ) = 1` using `rfl`. Establish `f3 : ((3 : Fin 8) : ℕ) = 3` using `rfl`. Establish `f5 : ((5 : Fin 8) : ℕ) = 5` using `rfl`. Establish `f7 : ((7 : Fin 8) : ℕ) = 7` using `rfl`. Rewrite using `[f1, f3, f5, f7]`.

Simplify using `only [Int.cast_zero, Int.cast_one, Int.cast_neg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem LFunction_eq_of_one_lt (χ : DirichletCharacter ℂ 8)
    (hχ : ∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ)) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = ∑' k, br 8 1 3 k s - ∑' k, br 8 5 7 k s := by
  have hs0 : 0 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← (summable_br (by norm_num) le_rfl (by norm_num) hs0).tsum_sub
      (summable_br (by norm_num) (by norm_num) (by norm_num) hs0)]
  have h0 : HasSum (LSeries.term (fun n : ℕ => χ n) s) (LSeries (fun n : ℕ => χ n) s) :=
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum
  rw [← (hasSum_group 8 h0).tsum_eq]
  refine tsum_congr fun k => ?_
  have ht : ∀ j : ℕ, LSeries.term (fun n : ℕ => χ n) s (8 * k + j) =
      ((ZMod.χ₈ (j : ZMod 8) : ℤ) : ℂ) * ((8 * k + j : ℕ) : ℂ) ^ (-s) := by
    intro j
    have hc : ((8 * k + j : ℕ) : ZMod 8) = (j : ZMod 8) := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    rw [LSeries.term_def₀ (by rw [Nat.cast_zero, hχ]; simp), hc, hχ]
  simp only [ht, Fin.sum_univ_eight, br]
  have e0 : ZMod.χ₈ (((0 : Fin 8) : ℕ) : ZMod 8) = 0 := by decide
  have e1 : ZMod.χ₈ (((1 : Fin 8) : ℕ) : ZMod 8) = 1 := by decide
  have e2 : ZMod.χ₈ (((2 : Fin 8) : ℕ) : ZMod 8) = 0 := by decide
  have e3 : ZMod.χ₈ (((3 : Fin 8) : ℕ) : ZMod 8) = -1 := by decide
  have e4 : ZMod.χ₈ (((4 : Fin 8) : ℕ) : ZMod 8) = 0 := by decide
  have e5 : ZMod.χ₈ (((5 : Fin 8) : ℕ) : ZMod 8) = -1 := by decide
  have e6 : ZMod.χ₈ (((6 : Fin 8) : ℕ) : ZMod 8) = 0 := by decide
  have e7 : ZMod.χ₈ (((7 : Fin 8) : ℕ) : ZMod 8) = 1 := by decide
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  have f1 : ((1 : Fin 8) : ℕ) = 1 := rfl
  have f3 : ((3 : Fin 8) : ℕ) = 3 := rfl
  have f5 : ((5 : Fin 8) : ℕ) = 5 := rfl
  have f7 : ((7 : Fin 8) : ℕ) = 7 := rfl
  rw [f1, f3, f5, f7]
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg]
  ring

/- English proof (translation)
Establish `hne : χ ≠ 1`. Introduce `h`. Establish `h3` using `hχ 3`. Establish `hu : IsUnit (3 : ZMod 8)` using `by decide`. Establish `e3 : ZMod.χ₈ (3 : ZMod 8) = -1` using `by decide`.

Rewrite `h3` using `[h, MulChar.one_apply hu, e3]`. Evaluate the numerical expressions using `at h3`. Establish `ho : IsOpen {s : ℂ | 0 < s.re}` using `isOpen_lt continuous_const continuous_re`. Establish `hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re}` using `(DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho`. Establish `hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 8 1 3 k s - ∑' k, br 8 5 7 k s) {s | 0 < s.re}` using `((differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).sub (differentiableOn_tsum_br (by norm_num) (by norm_num) (by norm_num))).analyticOnNhd ho`.

Establish `hA` using `hF.eqOn_of_preconnected_of_eventuallyEq hG convex_re_pos.isPreconnected (z₀ := 2) (by simp) (by filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz using LFunction_eq_of_one_lt χ hχ hz)`. Establish `hs0 : 0 < (σ : ℂ).re` using `by simpa using h0`. Establish `key : DirichletCharacter.LFunction χ σ = ∑' k, br 8 1 3 k σ - ∑' k, br 8 5 7 k σ` using `hA hs0`. Establish `s1` using `summable_br (N := 8) (c := 1) (d := 3) (by norm_num) le_rfl (by norm_num) hs0`. Establish `s2` using `summable_br (N := 8) (c := 5) (d := 7) (by norm_num) (by norm_num) (by norm_num) hs0`.

Simplify using `only [br_ofReal] at key s1 s2`. Rewrite `s1`, `s2` using `[summable_ofReal]`. Rewrite `key` using `[← ofReal_tsum, ← ofReal_tsum, ← ofReal_sub]`. Rewrite using `[key, ofReal_ne_zero]`. Establish `hlt : ∀ k : ℕ, ((8 * k + 5 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 7 : ℕ) : ℝ) ^ (-σ) < ((8 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 3 : ℕ) : ℝ) ^ (-σ)`.

Introduce `k`. Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Use `strictAntiOn_diff h0 (a := 8 * k + 1) (b := 8 * k + 5) (by rw [Set.mem_Ioi]; linarith) (by rw [Set.mem_Ioi]; linarith) (by linarith)` as an intermediate fact. Simplify using `only at this`. Use `push_cast`.

Rewrite using `[show (8 * k + 7 : ℝ) = 8 * k + 5 + 2 by ring, show (8 * k + 3 : ℝ) = 8 * k + 1 + 2 by ring]`. Conclude with `this`. Conclude with `(sub_pos.mpr (s2.tsum_lt_tsum (i := 0) (fun k => (hlt k).le) (hlt 0) s1)).ne'`.
-/
theorem LFunction_chi8_ne_zero (χ : DirichletCharacter ℂ 8)
    (hχ : ∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ)) (σ : ℝ) (h0 : 0 < σ) :
    DirichletCharacter.LFunction χ σ ≠ 0 := by
  have hne : χ ≠ 1 := by
    intro h
    have h3 := hχ 3
    have hu : IsUnit (3 : ZMod 8) := by decide
    have e3 : ZMod.χ₈ (3 : ZMod 8) = -1 := by decide
    rw [h, MulChar.one_apply hu, e3] at h3
    norm_num at h3
  have ho : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hne).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (fun s => ∑' k, br 8 1 3 k s - ∑' k, br 8 5 7 k s) {s | 0 < s.re} :=
    ((differentiableOn_tsum_br (by norm_num) le_rfl (by norm_num)).sub
      (differentiableOn_tsum_br (by norm_num) (by norm_num) (by norm_num))).analyticOnNhd ho
  have hA := hF.eqOn_of_preconnected_of_eventuallyEq hG convex_re_pos.isPreconnected
    (z₀ := 2) (by simp)
    (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz using LFunction_eq_of_one_lt χ hχ hz)
  have hs0 : 0 < (σ : ℂ).re := by simpa using h0
  have key : DirichletCharacter.LFunction χ σ = ∑' k, br 8 1 3 k σ - ∑' k, br 8 5 7 k σ := hA hs0
  have s1 := summable_br (N := 8) (c := 1) (d := 3) (by norm_num) le_rfl (by norm_num) hs0
  have s2 := summable_br (N := 8) (c := 5) (d := 7) (by norm_num) (by norm_num) (by norm_num) hs0
  simp only [br_ofReal] at key s1 s2
  rw [summable_ofReal] at s1 s2
  rw [← ofReal_tsum, ← ofReal_tsum, ← ofReal_sub] at key
  rw [key, ofReal_ne_zero]
  have hlt : ∀ k : ℕ, ((8 * k + 5 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 7 : ℕ) : ℝ) ^ (-σ) <
      ((8 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((8 * k + 3 : ℕ) : ℝ) ^ (-σ) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := strictAntiOn_diff h0 (a := 8 * k + 1) (b := 8 * k + 5)
      (by rw [Set.mem_Ioi]; linarith) (by rw [Set.mem_Ioi]; linarith) (by linarith)
    simp only at this
    push_cast
    rw [show (8 * k + 7 : ℝ) = 8 * k + 5 + 2 by ring, show (8 * k + 3 : ℝ) = 8 * k + 1 + 2 by ring]
    exact this
  exact (sub_pos.mpr (s2.tsum_lt_tsum (i := 0) (fun k => (hlt k).le) (hlt 0) s1)).ne'

/- English proof (translation)
Assemble the required witnesses or components as `⟨riemannZeta_ne_zero_of_mem_Ioo, LFunction_chi8_ne_zero⟩`.
-/
theorem no_real_zero :
    (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0) ∧
    ∀ (χ : DirichletCharacter ℂ 8), (∀ a : ZMod 8, χ a = ((ZMod.χ₈ a : ℤ) : ℂ)) →
      ∀ σ : ℝ, 0 < σ → DirichletCharacter.LFunction χ σ ≠ 0 :=
  ⟨riemannZeta_ne_zero_of_mem_Ioo, LFunction_chi8_ne_zero⟩

end GlobalTheory.RealZeros
