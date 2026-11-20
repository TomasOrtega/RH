import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

namespace GeodesicCounting

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

end GeodesicCounting

/- English proof (translation)
Distinguish the cases in `hz : z = 0`. Simplify using `[hz]`. Conclude with `((hh w).re_dotProduct_pos hz).le`.
-/
private theorem re_star_dotProduct_mat_mulVec_nonneg_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) (w : InfinitePlace L) (z : Fin N → ℂ) :
    0 ≤ (star z ⬝ᵥ mat h w *ᵥ z).re := by
  by_cases hz : z = 0
  · simp [hz]
  · exact ((hh w).re_dotProduct_pos hz).le

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun w _ => re_star_dotProduct_mat_mulVec_nonneg_of_mem_Pos hh w (x w)`.
-/
private theorem qR_nonneg_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) (x : InfinitePlace L → Fin N → ℂ) : 0 ≤ qR h x :=
  Finset.sum_nonneg fun w _ => re_star_dotProduct_mat_mulVec_nonneg_of_mem_Pos hh w (x w)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : ∃ w, x w ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (funext hc)`. Conclude with `Finset.sum_pos' (fun w _ => re_star_dotProduct_mat_mulVec_nonneg_of_mem_Pos hh w (x w)) ⟨w₀, Finset.mem_univ _, (hh w₀).re_dotProduct_pos hw₀⟩`.
-/
private theorem qR_pos_of_mem_Pos_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) (x : InfinitePlace L → Fin N → ℂ) (hx : x ≠ 0) : 0 < qR h x := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, x w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  exact Finset.sum_pos' (fun w _ => re_star_dotProduct_mat_mulVec_nonneg_of_mem_Pos hh w (x w))
    ⟨w₀, Finset.mem_univ _, (hh w₀).re_dotProduct_pos hw₀⟩

/- English proof (translation)
Use `show ∑ w, (star ((x + y) w) ⬝ᵥ mat h w *ᵥ (x + y) w).re + ∑ w, (star ((x - y) w) ⬝ᵥ mat h w *ᵥ (x - y) w).re = 2 * ∑ w, (star (x w) ⬝ᵥ mat h w *ᵥ x w).re + 2 * ∑ w, (star (y w) ⬝ᵥ mat h w *ᵥ y w).re`. Rewrite using `[← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.sub_apply, star_add, star_sub, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct, Complex.add_re, Complex.sub_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem qR_parallelogram {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (x y : InfinitePlace L → Fin N → ℂ) :
    qR h (x + y) + qR h (x - y) = 2 * qR h x + 2 * qR h y := by
  show ∑ w, (star ((x + y) w) ⬝ᵥ mat h w *ᵥ (x + y) w).re +
      ∑ w, (star ((x - y) w) ⬝ᵥ mat h w *ᵥ (x - y) w).re =
    2 * ∑ w, (star (x w) ⬝ᵥ mat h w *ᵥ x w).re + 2 * ∑ w, (star (y w) ⬝ᵥ mat h w *ᵥ y w).re
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, star_add, star_sub, Matrix.mulVec_add, Matrix.mulVec_sub,
    dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct, Complex.add_re, Complex.sub_re]
  ring

/- English proof (translation)
Use `show ∑ w, (star ((c • x) w) ⬝ᵥ mat h w *ᵥ (c • x) w).re = c ^ 2 * ∑ w, (star (x w) ⬝ᵥ mat h w *ᵥ x w).re`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, star_trivial]`. Simplify using `[Complex.smul_re, pow_two, mul_assoc]`.
-/
private theorem qR_smul_place_vec {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (x : InfinitePlace L → Fin N → ℂ) : qR h (c • x) = c ^ 2 * qR h x := by
  show ∑ w, (star ((c • x) w) ⬝ᵥ mat h w *ᵥ (c • x) w).re =
    c ^ 2 * ∑ w, (star (x w) ⬝ᵥ mat h w *ᵥ x w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    star_trivial]
  simp [Complex.smul_re, pow_two, mul_assoc]

/- English proof (translation)
Use `qR_parallelogram h (x - a) a` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Use `qR_nonneg_of_mem_Pos hh (x - a - a)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem qR_le_two_mul_qR_sub_add_two_mul_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) (x a : InfinitePlace L → Fin N → ℂ) :
    qR h x ≤ 2 * qR h (x - a) + 2 * qR h a := by
  have := qR_parallelogram h (x - a) a
  rw [sub_add_cancel] at this
  have := qR_nonneg_of_mem_Pos hh (x - a - a)
  linarith

/- English proof (translation)
Unfold `qR`. Use `fun_prop`.
-/
private theorem continuous_qR_place_vec {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    Continuous (fun x : InfinitePlace L → Fin N → ℂ => qR h x) := by
  unfold qR
  fun_prop

/- English proof (translation)
Establish `key : ∀ (m : ℝ), (∀ u ∈ Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1, m ≤ qR h u) → ∀ x : InfinitePlace L → Fin N → ℂ, m * ‖x‖ ^ 2 ≤ qR h x`. Introduce `m hm x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Use `qR_smul_place_vec h 0 0` as an intermediate fact.

Simplify using `only [zero_smul] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.2 hx`. Establish `hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1`.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Establish `e : x = ‖x‖ • (‖x‖⁻¹ • x)` using `by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]`. Use `hm _ hu` as an intermediate fact. Use `conv_rhs => rw [e]`. Rewrite using `[qR_smul_place_vec]`.

Use polynomial arithmetic with `[sq_nonneg ‖x‖]`. Distinguish the cases in `hE : (Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1).Nonempty`. Take `⟨x₀, hx₀, hmin⟩` from `(isCompact_sphere (0 : InfinitePlace L → Fin N → ℂ) 1).exists_isMinOn hE (continuous_qR_place_vec h).continuousOn`. Establish `hx₀0 : x₀ ≠ 0`. Introduce `e`.

Rewrite `hx₀` using `[e, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hx₀`. Conclude with `⟨qR h x₀, qR_pos_of_mem_Pos_of_ne_zero hh x₀ hx₀0, key _ fun u hu => hmin hu⟩`. Use `⟨1, one_pos, key 1 fun u hu => absurd ⟨u, hu⟩ hE⟩` and prove the remaining obligations.
-/
private theorem exists_pos_mul_norm_sq_le_qR_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) : ∃ m : ℝ, 0 < m ∧
      ∀ x : InfinitePlace L → Fin N → ℂ, m * ‖x‖ ^ 2 ≤ qR h x := by
  have key : ∀ (m : ℝ), (∀ u ∈ Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1, m ≤ qR h u) →
      ∀ x : InfinitePlace L → Fin N → ℂ, m * ‖x‖ ^ 2 ≤ qR h x := by
    intro m hm x
    by_cases hx : x = 0
    · subst hx
      have := qR_smul_place_vec h 0 0
      simp only [zero_smul] at this
      rw [this]
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have e : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have := hm _ hu
      conv_rhs => rw [e]
      rw [qR_smul_place_vec]
      nlinarith [sq_nonneg ‖x‖]
  by_cases hE : (Metric.sphere (0 : InfinitePlace L → Fin N → ℂ) 1).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : InfinitePlace L → Fin N → ℂ) 1).exists_isMinOn hE
      (continuous_qR_place_vec h).continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      intro e
      rw [e, mem_sphere_zero_iff_norm, norm_zero] at hx₀
      exact zero_ne_one hx₀
    exact ⟨qR h x₀, qR_pos_of_mem_Pos_of_ne_zero hh x₀ hx₀0, key _ fun u hu => hmin hu⟩
  · refine ⟨1, one_pos, key 1 fun u hu => absurd ⟨u, hu⟩ hE⟩
/- English proof (translation)
Establish `h0 : qR h (0 : InfinitePlace L → Fin N → ℂ) = 0`. Use `qR_smul_place_vec h 0 0` as an intermediate fact. Simplify using `using this`. Prove the components needed by the constructor for the conclusion. Conclude with `(isOpen_lt (continuous_qR_place_vec h) continuous_const).measure_pos _ ⟨0, by simp only [Set.mem_setOf_eq, h0, hr]⟩`.

Take `⟨m, hm, hb⟩` from `exists_pos_mul_norm_sq_le_qR_of_mem_Pos hh`. Establish `sub : {x : InfinitePlace L → Fin N → ℂ | qR h x < r} ⊆ Metric.closedBall 0 (√(r / m))`. Introduce `x hx`. Rewrite using `[mem_closedBall_zero_iff]`. Establish `h1` using `hb x`.

Establish `h2 : ‖x‖ ^ 2 ≤ r / m`. Rewrite using `[le_div_iff₀ hm]`. Establish `: qR h x < r` using `hx`. Use the polynomial consequences of the given equalities and inequalities. Use `Real.abs_le_sqrt h2` as an intermediate fact.

Rewrite `this` using `[abs_of_nonneg (norm_nonneg x)]`. Then use the resulting hypothesis. Conclude with `(MeasureTheory.measure_mono sub).trans_lt MeasureTheory.measure_closedBall_lt_top`.
-/
private theorem addHaar_qR_lt_pos_and_lt_top_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {r : ℝ} (hr : 0 < r) :
    0 < (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h x < r} ∧
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h x < r} < ⊤ := by
  have h0 : qR h (0 : InfinitePlace L → Fin N → ℂ) = 0 := by
    have := qR_smul_place_vec h 0 0
    simpa using this
  constructor
  · exact (isOpen_lt (continuous_qR_place_vec h) continuous_const).measure_pos _
      ⟨0, by simp only [Set.mem_setOf_eq, h0, hr]⟩
  · obtain ⟨m, hm, hb⟩ := exists_pos_mul_norm_sq_le_qR_of_mem_Pos hh
    have sub : {x : InfinitePlace L → Fin N → ℂ | qR h x < r} ⊆ Metric.closedBall 0 (√(r / m)) := by
      intro x hx
      rw [mem_closedBall_zero_iff]
      have h1 := hb x
      have h2 : ‖x‖ ^ 2 ≤ r / m := by
        rw [le_div_iff₀ hm]
        have : qR h x < r := hx
        nlinarith
      have := Real.abs_le_sqrt h2
      rwa [abs_of_nonneg (norm_nonneg x)] at this
    exact (MeasureTheory.measure_mono sub).trans_lt MeasureTheory.measure_closedBall_lt_top

/- English proof (translation)
Establish `e : {x : InfinitePlace L → Fin N → ℂ | qR h x < c ^ 2 * r} = (fun x : InfinitePlace L → Fin N → ℂ => c⁻¹ • x) ⁻¹' {x : InfinitePlace L → Fin N → ℂ | qR h x < r}`. Use extensionality with `x`. Rewrite using `[Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, qR_smul_place_vec]`. Establish `hc2 : 0 < c ^ 2` using `by positivity`. Rewrite using `[inv_pow, inv_mul_lt_iff₀ hc2]`.

Rewrite using `[e, MeasureTheory.Measure.addHaar_preimage_smul _ (inv_ne_zero hc.ne'), inv_pow, inv_inv, abs_of_pos (by positivity)]`.
-/
private theorem addHaar_qR_lt_sq_mul_eq_pow_mul {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h x < c ^ 2 * r} =
      ENNReal.ofReal (c ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)) *
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
          {x | qR h x < r} := by
  have e : {x : InfinitePlace L → Fin N → ℂ | qR h x < c ^ 2 * r} =
      (fun x : InfinitePlace L → Fin N → ℂ => c⁻¹ • x) ⁻¹'
        {x : InfinitePlace L → Fin N → ℂ | qR h x < r} := by
    ext x
    rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq, qR_smul_place_vec]
    have hc2 : 0 < c ^ 2 := by positivity
    rw [inv_pow, inv_mul_lt_iff₀ hc2]
  rw [e, MeasureTheory.Measure.addHaar_preimage_smul _ (inv_ne_zero hc.ne'), inv_pow, inv_inv,
    abs_of_pos (by positivity)]

/- English proof (translation)
Establish `e : {x : InfinitePlace L → Fin N → ℂ | qR h (x - a) < r} = (fun x => -a + x) ⁻¹' {x : InfinitePlace L → Fin N → ℂ | qR h x < r}`. Use extensionality with `x`. Simplify using `[sub_eq_neg_add]`. Rewrite using `[e, MeasureTheory.measure_preimage_add]`.
-/
private theorem addHaar_qR_sub_lt_eq_addHaar_qR_lt {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (a : InfinitePlace L → Fin N → ℂ) (r : ℝ) :
    (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h (x - a) < r} =
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h x < r} := by
  have e : {x : InfinitePlace L → Fin N → ℂ | qR h (x - a) < r} =
      (fun x => -a + x) ⁻¹' {x : InfinitePlace L → Fin N → ℂ | qR h x < r} := by
    ext x
    simp [sub_eq_neg_add]
  rw [e, MeasureTheory.measure_preimage_add]
/- English proof (translation)
Use `qR_smul_place_vec h (-1) z` as an intermediate fact. Rewrite `this` using `[neg_one_smul, neg_one_sq, one_mul]`. Then use the resulting hypothesis.
-/
private theorem qR_neg {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (z : InfinitePlace L → Fin N → ℂ) : qR h (-z) = qR h z := by
  have := qR_smul_place_vec h (-1) z
  rwa [neg_one_smul, neg_one_sq, one_mul] at this

/- English proof (translation)
Establish `hq : ∀ v : UpperTheory.V.KT.Lat L N, q h v = qR h (toR v)` using `fun v => rfl`. Establish `htoR : ∀ u v : UpperTheory.V.KT.Lat L N, toR (u - v) = toR u - toR v`. Introduce `u v`. Unfold `toR`. Use extensionality with `w a`.

Simplify using the standard rewrite rules. Establish `hr : 0 < s / 4` using `by positivity`. Establish `hc : 0 < √(8 * ρ + 2)` using `Real.sqrt_pos.2 (by linarith)`. Establish `hc2 : √(8 * ρ + 2) ^ 2 = 8 * ρ + 2` using `Real.sq_sqrt (by linarith)`. Take `⟨hpos, hfin⟩` from `addHaar_qR_lt_pos_and_lt_top_of_mem_Pos hh hr`.

Establish `hmeas : ∀ a : InfinitePlace L → Fin N → ℂ, MeasurableSet {x : InfinitePlace L → Fin N → ℂ | qR h (x - a) < s / 4}` using `fun a => (isOpen_lt ((continuous_qR_place_vec h).comp (continuous_id.sub continuous_const)) continuous_const).measurableSet`. Establish `hbig : MeasurableSet {x : InfinitePlace L → Fin N → ℂ | qR h x < √(8 * ρ + 2) ^ 2 * (s / 4)}` using `(isOpen_lt (continuous_qR_place_vec h) continuous_const).measurableSet`. Establish `point : ∀ x : InfinitePlace L → Fin N → ℂ, ∑ v ∈ hS.toFinset, {y : InfinitePlace L → Fin N → ℂ | qR h (y - toR v) < s / 4}.indicator (1 : (InfinitePlace L → Fin N → ℂ) → ENNReal) x ≤ (hT.toFinset.card : ENNReal) * {y : InfinitePlace L → Fin N → ℂ | qR h y < √(8 * ρ + 2) ^ 2 * (s …`. Introduce `x`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`.

Rewrite using `[Finset.sum_boole]`. Distinguish the cases in `hne : (hS.toFinset.filter fun v => qR h (x - toR v) < s / 4).Nonempty`. Take `⟨v₀, hv₀⟩` from `hne`. Rewrite `hv₀` using `[Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Establish `hx : qR h x < √(8 * ρ + 2) ^ 2 * (s / 4)`.

Use `qR_le_two_mul_qR_sub_add_two_mul_of_mem_Pos hh x (toR v₀)` as an intermediate fact. Rewrite using `[hc2]`. Rewrite `hv₀` using `[hq]`. Use polynomial arithmetic with `[hv₀.1, hv₀.2]`. Rewrite using `[if_pos hx, mul_one, Nat.cast_le]`.

Use `Finset.card_le_card_of_injOn (fun v => v - v₀) ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv` using `[Finset.coe_filter]`. Take `⟨-, hv⟩` from `hv`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hq, htoR]`.

Establish `e : toR v - toR v₀ = (x - toR v₀) - (x - toR v)` using `by abel`. Establish `h1` using `qR_le_two_mul_qR_sub_add_two_mul_of_mem_Pos hh (toR v - toR v₀) (x - toR v₀)`. Establish `e2 : toR v - toR v₀ - (x - toR v₀) = -(x - toR v)` using `by abel`. Rewrite `h1` using `[e2, qR_neg]`. Combine the linear relations using `[hv₀.2]`.

Introduce `a _ b _ hab`. Conclude with `sub_left_injective hab`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Rewrite using `[hne, Finset.card_empty, Nat.cast_zero]`. Conclude with `bot_le`.

Establish `key : (hS.toFinset.card : ENNReal) * (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) {x | qR h x < s / 4} ≤ (hT.toFinset.card : ENNReal) * (ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)) * (MeasureTheory.Measur …`. Rewrite using `[← addHaar_qR_lt_sq_mul_eq_pow_mul h hc]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [addHaar_qR_sub_lt_eq_addHaar_qR_lt, Finset.sum_const, nsmul_eq_mul]`. Use `_ = ∫⁻ x, ∑ v ∈ hS.toFinset, {y : InfinitePlace L → Fin N → ℂ | qR h (y - toR v) < s / 4}.indicator 1 x ∂(MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) := by`.

Rewrite using `[MeasureTheory.lintegral_finset_sum _ fun v _ => (measurable_one.indicator (hmeas (toR v)))]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[MeasureTheory.lintegral_indicator_one (hmeas (toR v))]`. Use `_ ≤ ∫⁻ x, (hT.toFinset.card : ENNReal) * {y : InfinitePlace L → Fin N → ℂ | qR h y < √(8 * ρ + 2) ^ 2 * (s / 4)}.indicator 1 x ∂(MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) := MeasureTheory.lintegral_mono point`. Use `_ = (hT.toFinset.card : ENNReal) * (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) {x | qR h x < √(8 * ρ + 2) ^ 2 * (s / 4)} := by`.

Rewrite using `[MeasureTheory.lintegral_const_mul _ (measurable_one.indicator hbig), MeasureTheory.lintegral_indicator_one hbig]`. Rewrite `key` using `[← mul_assoc]`. Establish `key2` using `(ENNReal.mul_le_mul_iff_left hpos.ne' hfin.ne).1 key`. Rewrite using `[Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]`. Establish `e1 : ((hS.toFinset.card : ℕ) : ENNReal) = ENNReal.ofReal (hS.toFinset.card : ℝ)`.

Rewrite using `[ENNReal.ofReal_natCast]`. Establish `e2 : ((hT.toFinset.card : ℕ) : ENNReal) * ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)) = ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ) * (hT.toFinset.card : ℝ))`. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_comm]`. Rewrite `key2` using `[e1, e2, ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Conclude with `key2`.
-/
private theorem ncard_q_le_mul_le_sqrt_pow_mul_ncard {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {ρ s : ℝ} (hs : 0 < s) (hρ : 0 ≤ ρ)
    (hS : {v : UpperTheory.V.KT.Lat L N | q h v ≤ ρ * s}.Finite)
    (hT : {v : UpperTheory.V.KT.Lat L N | q h v ≤ s}.Finite) :
    ({v : UpperTheory.V.KT.Lat L N | q h v ≤ ρ * s}.ncard : ℝ) ≤
      √(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ) *
        {v : UpperTheory.V.KT.Lat L N | q h v ≤ s}.ncard := by
  have hq : ∀ v : UpperTheory.V.KT.Lat L N, q h v = qR h (toR v) := fun v => rfl
  have htoR : ∀ u v : UpperTheory.V.KT.Lat L N, toR (u - v) = toR u - toR v := by
    intro u v
    unfold toR
    ext w a
    simp
  have hr : 0 < s / 4 := by positivity
  have hc : 0 < √(8 * ρ + 2) := Real.sqrt_pos.2 (by linarith)
  have hc2 : √(8 * ρ + 2) ^ 2 = 8 * ρ + 2 := Real.sq_sqrt (by linarith)
  obtain ⟨hpos, hfin⟩ := addHaar_qR_lt_pos_and_lt_top_of_mem_Pos hh hr
  have hmeas : ∀ a : InfinitePlace L → Fin N → ℂ,
      MeasurableSet {x : InfinitePlace L → Fin N → ℂ | qR h (x - a) < s / 4} := fun a =>
    (isOpen_lt ((continuous_qR_place_vec h).comp (continuous_id.sub continuous_const))
      continuous_const).measurableSet
  have hbig : MeasurableSet
      {x : InfinitePlace L → Fin N → ℂ | qR h x < √(8 * ρ + 2) ^ 2 * (s / 4)} :=
    (isOpen_lt (continuous_qR_place_vec h) continuous_const).measurableSet
  have point : ∀ x : InfinitePlace L → Fin N → ℂ,
      ∑ v ∈ hS.toFinset, {y : InfinitePlace L → Fin N → ℂ | qR h (y - toR v) < s / 4}.indicator
        (1 : (InfinitePlace L → Fin N → ℂ) → ENNReal) x ≤
      (hT.toFinset.card : ENNReal) *
        {y : InfinitePlace L → Fin N → ℂ | qR h y < √(8 * ρ + 2) ^ 2 * (s / 4)}.indicator 1 x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    rw [Finset.sum_boole]
    by_cases hne : (hS.toFinset.filter fun v => qR h (x - toR v) < s / 4).Nonempty
    · obtain ⟨v₀, hv₀⟩ := hne
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv₀
      have hx : qR h x < √(8 * ρ + 2) ^ 2 * (s / 4) := by
        have := qR_le_two_mul_qR_sub_add_two_mul_of_mem_Pos hh x (toR v₀)
        rw [hc2]
        rw [hq] at hv₀
        nlinarith [hv₀.1, hv₀.2]
      rw [if_pos hx, mul_one, Nat.cast_le]
      refine Finset.card_le_card_of_injOn (fun v => v - v₀) ?_ ?_
      · intro v hv
        rw [Finset.coe_filter] at hv
        obtain ⟨-, hv⟩ := hv
        rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hq, htoR]
        have e : toR v - toR v₀ = (x - toR v₀) - (x - toR v) := by abel
        have h1 := qR_le_two_mul_qR_sub_add_two_mul_of_mem_Pos hh (toR v - toR v₀) (x - toR v₀)
        have e2 : toR v - toR v₀ - (x - toR v₀) = -(x - toR v) := by abel
        rw [e2, qR_neg] at h1
        linarith [hv₀.2]
      · intro a _ b _ hab
        exact sub_left_injective hab
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.card_empty, Nat.cast_zero]
      exact bot_le
  have key : (hS.toFinset.card : ENNReal) *
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
        {x | qR h x < s / 4} ≤
      (hT.toFinset.card : ENNReal) *
        (ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)) *
        (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
          {x | qR h x < s / 4}) := by
    rw [← addHaar_qR_lt_sq_mul_eq_pow_mul h hc]
    calc (hS.toFinset.card : ENNReal) *
          (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
            {x | qR h x < s / 4}
        = ∑ v ∈ hS.toFinset,
            (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
              {x | qR h (x - toR v) < s / 4} := by
          simp only [addHaar_qR_sub_lt_eq_addHaar_qR_lt, Finset.sum_const, nsmul_eq_mul]
      _ = ∫⁻ x, ∑ v ∈ hS.toFinset,
            {y : InfinitePlace L → Fin N → ℂ | qR h (y - toR v) < s / 4}.indicator 1 x
            ∂(MeasureTheory.Measure.addHaar :
              MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) := by
          rw [MeasureTheory.lintegral_finset_sum _ fun v _ =>
            (measurable_one.indicator (hmeas (toR v)))]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [MeasureTheory.lintegral_indicator_one (hmeas (toR v))]
      _ ≤ ∫⁻ x, (hT.toFinset.card : ENNReal) *
            {y : InfinitePlace L → Fin N → ℂ | qR h y < √(8 * ρ + 2) ^ 2 * (s / 4)}.indicator 1 x
            ∂(MeasureTheory.Measure.addHaar :
              MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ)) :=
          MeasureTheory.lintegral_mono point
      _ = (hT.toFinset.card : ENNReal) *
          (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (InfinitePlace L → Fin N → ℂ))
            {x | qR h x < √(8 * ρ + 2) ^ 2 * (s / 4)} := by
          rw [MeasureTheory.lintegral_const_mul _ (measurable_one.indicator hbig),
            MeasureTheory.lintegral_indicator_one hbig]
  rw [← mul_assoc] at key
  have key2 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin.ne).1 key
  rw [Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]
  have e1 : ((hS.toFinset.card : ℕ) : ENNReal) = ENNReal.ofReal (hS.toFinset.card : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have e2 : ((hT.toFinset.card : ℕ) : ENNReal) *
      ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)) =
      ENNReal.ofReal (√(8 * ρ + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ) *
        (hT.toFinset.card : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_comm]
  rw [e1, e2, ENNReal.ofReal_le_ofReal_iff (by positivity)] at key2
  exact key2

open GeodesicCounting in
/- English proof (translation)
Unfold `GCount Basic Count`. Introduce `hB L _ _ N R`. Use `⟨√(8 * max R 1 + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ), by positivity, ?_⟩` and prove the remaining obligations. Introduce `h hh s hs`. Establish `hfin : ∀ B : ℝ, {v : UpperTheory.V.KT.Lat L N | q h v ≤ B}.Finite`.

Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Introduce `B`. Conclude with `Set.toFinite _`. Conclude with `((hB L N hN).1 h hh).2.2.2.2`. Establish `hC : 1 ≤ √(8 * max R 1 + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ)`.

Apply `one_le_pow₀` to reduce the goal to its premises. Rewrite using `[Real.one_le_sqrt]`. Use `le_max_right R 1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Break down `hs.eq_or_lt with rfl | hs'` into its components or cases.

Rewrite using `[mul_zero]`. Conclude with `le_mul_of_one_le_left (Nat.cast_nonneg _) hC`. Establish `sub : {v : UpperTheory.V.KT.Lat L N | q h v ≤ R * s} ⊆ {v | q h v ≤ max R 1 * s}` using `fun v hv => le_trans hv (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem pf_GCount : GCount := by
  unfold GCount Basic Count
  intro hB L _ _ N R
  refine ⟨√(8 * max R 1 + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ), by positivity, ?_⟩
  intro h hh s hs
  have hfin : ∀ B : ℝ, {v : UpperTheory.V.KT.Lat L N | q h v ≤ B}.Finite := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · intro B
      exact Set.toFinite _
    · exact ((hB L N hN).1 h hh).2.2.2.2
  have hC : 1 ≤ √(8 * max R 1 + 2) ^ Module.finrank ℝ (InfinitePlace L → Fin N → ℂ) := by
    apply one_le_pow₀
    rw [Real.one_le_sqrt]
    have := le_max_right R 1
    linarith
  rcases hs.eq_or_lt with rfl | hs'
  · rw [mul_zero]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hC
  · have sub : {v : UpperTheory.V.KT.Lat L N | q h v ≤ R * s} ⊆ {v | q h v ≤ max R 1 * s} :=
      fun v hv => le_trans hv (mul_le_mul_of_nonneg_right (le_max_left _ _) hs)
    calc (({v : UpperTheory.V.KT.Lat L N | q h v ≤ R * s}.ncard : ℕ) : ℝ)
        ≤ ({v : UpperTheory.V.KT.Lat L N | q h v ≤ max R 1 * s}.ncard : ℝ) :=
          Nat.cast_le.2 (Set.ncard_le_ncard sub (hfin _))
      _ ≤ _ := ncard_q_le_mul_le_sqrt_pow_mul_ncard hh hs' (by positivity) (hfin _) (hfin _)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
