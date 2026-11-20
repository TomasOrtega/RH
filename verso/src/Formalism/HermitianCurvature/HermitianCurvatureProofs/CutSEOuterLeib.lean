import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

/- English proof (translation)
Unfold `wl`. Use `le_trans (norm_add_le _ _) (add_le_add ?_ ?_)` and prove the remaining obligations. Use `le_trans (norm_smul_le _ _) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `le_trans (norm_smul_le _ _) ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_wl_le (A B : ℂ) : ‖wl A B‖ ≤ ‖A‖ + ‖B‖ := by
  unfold wl
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (norm_smul_le _ _) ?_
    calc ‖A‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  · refine le_trans (norm_smul_le _ _) ?_
    calc ‖B‖ * ‖Complex.conjCLE.toContinuousLinearMap‖ ≤ ‖B‖ * 1 :=
          mul_le_mul_of_nonneg_left (le_of_eq Complex.conjCLE_norm) (norm_nonneg _)
      _ = ‖B‖ := mul_one _

/- English proof (translation)
Unfold `wl`. Rewrite using `[integral_add (hf.smul_const _) (hg.smul_const _), integral_smul_const, integral_smul_const]`.
-/
theorem integral_wl {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℂ} (hf : Integrable f ν)
    (hg : Integrable g ν) : ∫ x, wl (f x) (g x) ∂ν = wl (∫ x, f x ∂ν) (∫ x, g x ∂ν) := by
  unfold wl
  rw [integral_add (hf.smul_const _) (hg.smul_const _), integral_smul_const, integral_smul_const]

/- English proof (translation)
Unfold `wl`. Conclude with `(hf.smul_const _).add (hg.smul_const _)`.
-/
theorem aesm_wl {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℂ} (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g ν) : AEStronglyMeasurable (fun x => wl (f x) (g x)) ν := by
  unfold wl
  exact (hf.smul_const _).add (hg.smul_const _)

section Fin

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Use `choose ε hε F hF hb using fun i => h i t0 ht0`. Establish `hF0 : ∀ i c', 0 ≤ F i c'` using `fun i c' => (norm_nonneg _).trans (hb i t0 (Metric.mem_ball_self (hε i)) c')`. Establish `hS : 0 ≤ ∑ i, 1 / ε i` using `Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hε i)).le`. Establish `hpos : 0 < 1 + ∑ i, 1 / ε i` using `by linarith`. Use `⟨1 / (1 + ∑ i, 1 / ε i), div_pos one_pos hpos, fun c' => ∑ i, F i c', integrable_finsetSum _ fun i _ => hF i, ?_⟩` and prove the remaining obligations.

Introduce `s hs c' i`. Establish `hle : 1 / (1 + ∑ i, 1 / ε i) ≤ ε i`. Rewrite using `[div_le_iff₀ hpos]`. Establish `h1 : 1 / ε i ≤ ∑ j, 1 / ε j` using `Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.mpr (hε j)).le) (Finset.mem_univ i)`. Establish `h2 : ε i * (1 / ε i) = 1` using `by field_simp [(hε i).ne']`.

Combine the equalities or inequalities in the displayed calculation. Use `(hb i s (Metric.ball_subset_ball hle hs) c').trans ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => F j c') (fun j _ => hF0 j c') (Finset.mem_univ i)`.
-/
theorem slDom_fin {ι : Type*} [Fintype ι] (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)
    (Φ : ι → RadSp k r z z' π π') (h : ∀ i, SlDom μ l c (Φ i)) (t0 : ℂ) (ht0 : t0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧ ∀ s ∈ Metric.ball t0 ε, ∀ c' i,
      ‖wtI l.succ c' * pairAt μ (Φ i) (Φ i) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := by
  choose ε hε F hF hb using fun i => h i t0 ht0
  have hF0 : ∀ i c', 0 ≤ F i c' := fun i c' => (norm_nonneg _).trans (hb i t0 (Metric.mem_ball_self (hε i)) c')
  have hS : 0 ≤ ∑ i, 1 / ε i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hε i)).le
  have hpos : 0 < 1 + ∑ i, 1 / ε i := by linarith
  refine ⟨1 / (1 + ∑ i, 1 / ε i), div_pos one_pos hpos, fun c' => ∑ i, F i c',
    integrable_finsetSum _ fun i _ => hF i, ?_⟩
  intro s hs c' i
  have hle : 1 / (1 + ∑ i, 1 / ε i) ≤ ε i := by
    rw [div_le_iff₀ hpos]
    have h1 : 1 / ε i ≤ ∑ j, 1 / ε j :=
      Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.mpr (hε j)).le) (Finset.mem_univ i)
    have h2 : ε i * (1 / ε i) = 1 := by field_simp [(hε i).ne']
    calc (1 : ℝ) = ε i * (1 / ε i) := h2.symm
      _ ≤ ε i * ∑ j, 1 / ε j := mul_le_mul_of_nonneg_left h1 (hε i).le
      _ ≤ ε i * (1 + ∑ j, 1 / ε j) := by nlinarith [hε i]
  refine (hb i s (Metric.ball_subset_ball hle hs) c').trans ?_
  exact Finset.single_le_sum (f := fun j => F j c') (fun j _ => hF0 j c') (Finset.mem_univ i)

/- English proof (translation)
Take `⟨ε, hε, F, hF, hb⟩` from `h t ht`. Conclude with `hF.mono' ((wtI_measurable _).aestronglyMeasurable.mul (pairAt_measI μ _ Φ Φ _).aestronglyMeasurable) (Eventually.of_forall fun c' => hb t (Metric.mem_ball_self hε) c')`.
-/
theorem level_l2_of_slice_domination (μ : Measure (Mt k r)) [SFinite μ] (l : Fin r) (c : Fin r → ℂ) {Φ : RadSp k r z z' π π'}
    (h : SlDom μ l c Φ) {t : ℂ} (ht : t ≠ 0) : LevelSquareIntegrable μ l.succ Φ (Function.update c l t) := by
  obtain ⟨ε, hε, F, hF, hb⟩ := h t ht
  exact hF.mono' ((wtI_measurable _).aestronglyMeasurable.mul (pairAt_measI μ _ Φ Φ _).aestronglyMeasurable)
    (Eventually.of_forall fun c' => hb t (Metric.mem_ball_self hε) c')

/- English proof (translation)
Simplify using `[wOp]`.
-/
theorem wOp_nil (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') : wOp X l [] Φ = Φ := by
  simp [wOp]

/- English proof (translation)
Simplify using `[wOp, dT]`.
-/
theorem wOp_dT (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') :
    wOp X l [2, 0] Φ = dT X l Φ := by
  simp [wOp, dT]

/- English proof (translation)
Simplify using `[wOp, dTb]`.
-/
theorem wOp_dTb (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') :
    wOp X l [5, 3] Φ = dTb X l Φ := by
  simp [wOp, dTb]

/- English proof (translation)
The claim follows from `op_lc X l 2 _ (op_lc X l 0 _ h)`.
-/
theorem dT_lc_OuterLeib (X : ActualOps k r z z' π π') (l : Fin r) {Φ : RadSp k r z z' π π'} (h : Φ ∈ lcSub k r z z' π π') :
    dT X l Φ ∈ lcSub k r z z' π π' :=
  op_lc X l 2 _ (op_lc X l 0 _ h)

/- English proof (translation)
The claim follows from `op_lc X l 5 _ (op_lc X l 3 _ h)`.
-/
theorem dTb_lc_OuterLeib (X : ActualOps k r z z' π π') (l : Fin r) {Φ : RadSp k r z z' π π'} (h : Φ ∈ lcSub k r z z' π π') :
    dTb X l Φ ∈ lcSub k r z z' π π' :=
  op_lc X l 5 _ (op_lc X l 3 _ h)

/- English proof (translation)
Rewrite using `[norm_mul, norm_mul, norm_mul, ← mul_add]`. Conclude with `mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hΦ hΨ p) (norm_nonneg _)`.
-/
theorem norm_wpair_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (w : ℂ) (p : Fin r → ℂ) :
    ‖w * pairAt μ Φ Ψ p‖ ≤ ‖w * pairAt μ Φ Φ p‖ + ‖w * pairAt μ Ψ Ψ p‖ := by
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hΦ hΨ p) (norm_nonneg _)

end Fin

/- English proof (translation)
Introduce `k r z z' Wp Wq _ _ _ _ _ _ π π' X μ hμ l S _ _ u v c hc hu hv t ht`. Establish `: SFinite μ` using `sfinite_of_isHaarOn _ μ hμ`. Set `Φs : Ix S × Fin 6 → RadSp k r z z' π π'` to `fun q => ![u q.1, v q.1, dT X l (u q.1), dTb X l (u q.1), dT X l (v q.1), dTb X l (v q.1)] q.2`. Establish `hΦs : ∀ q, SlDom μ l c (Φs q)`. Introduce and unpack `⟨a, j⟩`.

Use `fin_cases j`. Simplify `(hu a).2 []` using `[Φs, wOp_nil]`. Simplify `(hv a).2 []` using `[Φs, wOp_nil]`. Simplify `(hu a).2 [2, 0]` using `[Φs, wOp_dT]`. Simplify `(hu a).2 [5, 3]` using `[Φs, wOp_dTb]`.

Simplify `(hv a).2 [2, 0]` using `[Φs, wOp_dT]`. Simplify `(hv a).2 [5, 3]` using `[Φs, wOp_dTb]`. Take `⟨ε0, hε0, F, hF, hb⟩` from `slDom_fin μ l c Φs hΦs t ht`. Establish `hF0 : ∀ c', 0 ≤ F c'` using `fun c' => (norm_nonneg _).trans (hb t (Metric.mem_ball_self hε0) c' (Classical.arbitrary _))`. Establish `lu : ∀ a, u a ∈ lcSub k r z z' π π'` using `fun a => (hu a).1`.

Establish `lv : ∀ a, v a ∈ lcSub k r z z' π π'` using `fun a => (hv a).1`. Establish `Iu : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (u a)) (Function.update c l s)` using `fun a js s hs => level_l2_of_slice_domination μ l c ((hu a).2 js) hs`. Establish `Iv : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (v a)) (Function.update c l s)` using `fun a js s hs => level_l2_of_slice_domination μ l c ((hv a).2 js) hs`. Establish `I0u : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (u a) (Function.update c l s)` using `fun a s hs => by`. Simplify `Iu a [] s hs` using `[wOp_nil]`.

Establish `I0v : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (v a) (Function.update c l s)` using `fun a s hs => by`. Simplify `Iv a [] s hs` using `[wOp_nil]`. Establish `ITu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (u a)) (Function.update c l s)` using `fun a s hs => by`. Simplify `Iu a [2, 0] s hs` using `[wOp_dT]`. Establish `ITv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (v a)) (Function.update c l s)` using `fun a s hs => by`.

Simplify `Iv a [2, 0] s hs` using `[wOp_dT]`. Establish `IBu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (u a)) (Function.update c l s)` using `fun a s hs => by`. Simplify `Iu a [5, 3] s hs` using `[wOp_dTb]`. Establish `IBv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (v a)) (Function.update c l s)` using `fun a s hs => by`. Simplify `Iv a [5, 3] s hs` using `[wOp_dTb]`.

Use `set A : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' => pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c') + pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c') with hA`. Use `set Bf : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' => pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c') + pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c') with hB`. Use `set F0 : ℂ → Cf r l.succ → ℂ := fun s c' => wtI l.succ c' * ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c') with hF0def`. Use `set F' : ℂ → Cf r l.succ → (ℂ →L[ℝ] ℂ) := fun s c' => wl (wtI l.succ c' * ∑ a, A a s c') (wtI l.succ c' * ∑ a, Bf a s c') with hF'def`. Establish `hε : 0 < min ε0 ‖t‖` using `lt_min hε0 (norm_pos_iff.mpr ht)`.

Establish `hne : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ≠ 0`. Introduce `s hs h0`. Rewrite `hs` using `[h0, Metric.mem_ball, dist_zero_left]`. Conclude with `(lt_irrefl _ (hs.trans_le (min_le_right _ _)))`. Establish `hball : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ∈ Metric.ball t ε0` using `fun s hs => Metric.ball_subset_ball (min_le_left _ _) hs`.

Establish `intF0 : ∀ s, s ≠ 0 → Integrable (F0 s)` using `fun s hs => formIntOuter_of_l2I μ hμ l.succ u v lu lv (Function.update c l s) (fun a => I0u a s hs) (fun a => I0v a s hs)`. Establish `hA1` using `formIntOuter_of_l2I μ hμ l.succ (fun a => dT X l (u a)) v (fun a => dT_lc_OuterLeib X l (lu a)) lv (Function.update c l t) (fun a => ITu a t ht) (fun a => I0v a t ht)`. Establish `hA2` using `formIntOuter_of_l2I μ hμ l.succ u (fun a => dTb X l (v a)) lu (fun a => dTb_lc_OuterLeib X l (lv a)) (Function.update c l t) (fun a => I0u a t ht) (fun a => IBv a t ht)`. Establish `hB1` using `formIntOuter_of_l2I μ hμ l.succ (fun a => dTb X l (u a)) v (fun a => dTb_lc_OuterLeib X l (lu a)) lv (Function.update c l t) (fun a => IBu a t ht) (fun a => I0v a t ht)`. Establish `hB2` using `formIntOuter_of_l2I μ hμ l.succ u (fun a => dT X l (v a)) lu (fun a => dT_lc_OuterLeib X l (lv a)) (Function.update c l t) (fun a => I0u a t ht) (fun a => ITv a t ht)`.

Establish `intA : Integrable (fun c' => wtI l.succ c' * ∑ a, A a t c')`. Use `(hA1.add hA2).congr (Eventually.of_forall fun c' => ?_)` and prove the remaining obligations. Simplify using `only [hA, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]`. Establish `intB : Integrable (fun c' => wtI l.succ c' * ∑ a, Bf a t c')`. Use `(hB1.add hB2).congr (Eventually.of_forall fun c' => ?_)` and prove the remaining obligations.

Simplify using `only [hB, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]`. Establish `hIA : ∫ c', wtI l.succ c' * ∑ a, A a t c' = form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) + form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t)`. Unfold `form`. Rewrite using `[← integral_add hA1 hA2]`. Use `integral_congr_ae (Eventually.of_forall fun c' => ?_)` and prove the remaining obligations.

Simplify using `only [hA, Finset.sum_add_distrib, mul_add, wtI]`. Establish `hIB : ∫ c', wtI l.succ c' * ∑ a, Bf a t c' = form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) + form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t)`. Unfold `form`. Rewrite using `[← integral_add hB1 hB2]`. Use `integral_congr_ae (Eventually.of_forall fun c' => ?_)` and prove the remaining obligations.

Simplify using `only [hB, Finset.sum_add_distrib, mul_add, wtI]`. Establish `key : HasFDerivAt (fun s => ∫ c', F0 s c') (∫ c', F' t c') t`. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun c' => 8 * (Fintype.card (Ix S) : ℝ) * F c') (Metric.ball_mem_nhds t hε) ?_ (intF0 t ht) (aesm_wl intA.aestronglyMeasurable intB.aestronglyMeasurable) ?_ (hF.const_mul _) ?_` and prove the remaining obligations. Conclude with `Filter.eventually_of_mem (Metric.ball_mem_nhds t hε) fun s hs => (intF0 s (hne s hs)).aestronglyMeasurable`. Use `Eventually.of_forall fun c' s hs => ?_` and prove the remaining obligations.

Establish `hs'` using `hball s hs`. Establish `hd : ∀ a j, ‖wtI l.succ c' * pairAt μ (Φs (a, j)) (Φs (a, j)) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `fun a j => hb s hs' c' (a, j)`. Establish `hAa : ∀ a, ‖wtI l.succ c' * A a s c'‖ ≤ 4 * F c'`. Introduce `a`. Establish `e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 0`.

Establish `e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 1`. Establish `e2 : ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (dT X l (u a)) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 2`. Establish `e5 : ‖wtI l.succ c' * pairAt μ (dTb X l (v a)) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 5`. Establish `p1` using `norm_wpair_le μ hμ (dT_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')`. Establish `p2` using `norm_wpair_le μ hμ (lu a) (dTb_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')`.

Establish `: ‖wtI l.succ c' * A a s c'‖ ≤ ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ + ‖wtI l.succ c' * pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖`. Simplify using `only [hA, mul_add]`. Conclude with `norm_add_le _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBa : ∀ a, ‖wtI l.succ c' * Bf a s c'‖ ≤ 4 * F c'`.

Introduce `a`. Establish `e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 0`. Establish `e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 1`. Establish `e3 : ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (dTb X l (u a)) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 3`. Establish `e4 : ‖wtI l.succ c' * pairAt μ (dT X l (v a)) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖ ≤ F c'` using `hd a 4`.

Establish `p1` using `norm_wpair_le μ hμ (dTb_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')`. Establish `p2` using `norm_wpair_le μ hμ (lu a) (dT_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')`. Establish `: ‖wtI l.succ c' * Bf a s c'‖ ≤ ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ + ‖wtI l.succ c' * pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖`. Simplify using `only [hB, mul_add]`. Conclude with `norm_add_le _ _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `sA : ‖wtI l.succ c' * ∑ a, A a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c')`. Rewrite using `[Finset.mul_sum]`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hAa a).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `sB : ‖wtI l.succ c' * ∑ a, Bf a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c')`. Rewrite using `[Finset.mul_sum]`. Use `(norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hBa a).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Use `Eventually.of_forall fun c' s hs => ?_` and prove the remaining obligations. Establish `hd : ∀ a ∈ (Finset.univ : Finset (Ix S)), HasFDerivAt (fun s => pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c')) (wl (A a s c') (Bf a s c')) s` using `fun a _ => hP k r z z' Wp Wq π π' X μ hμ l (u a) (v a) (lu a) (lv a) c hc c' s (hne s hs)`. Establish `hs2` using `(HasFDerivAt.sum hd).const_mul (wtI l.succ c')`. Establish `e1 : (fun x => F0 x c') = fun y => wtI l.succ c' * (∑ i, fun s => pairAt μ (u i) (v i) (glue l.succ (Function.update c l s) c')) y`. Use function extensionality and compare the values at `y`.

Simplify using `only [hF0def, Finset.sum_apply]`. Establish `e2 : F' s c' = wtI l.succ c' • ∑ i, wl (A i s c') (Bf i s c')`. Use `ContinuousLinearMap.ext fun h => ?_` and prove the remaining obligations. Simplify using `only [hF'def, wl_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]`. Establish `alg : ∀ (f g : Ix S → ℂ) (w h : ℂ), w * (∑ a, f a) * h + w * (∑ a, g a) * conj h = w * ∑ a, (f a * h + g a * conj h)`.

Introduce `f g w h`. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `alg (fun a => A a s c') (fun a => Bf a s c') _ _`. Rewrite using `[e1, e2]`.

Conclude with `hs2`. Establish `hfin : ∫ c', F' t c' = wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) + form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t)) (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) + form μ l.succ u (fun b => dT X l (v b)) (Function.upd …`. Rewrite using `[← hIA, ← hIB]`. Conclude with `integral_wl intA intB`. Rewrite `key` using `[hfin]`.

Conclude with `key`.
-/
theorem outerLeib_of (hP : PairAtDeriv) : OuterLeib := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' X μ hμ l S _ _ u v c hc hu hv t ht
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ

  let Φs : Ix S × Fin 6 → RadSp k r z z' π π' := fun q =>
    ![u q.1, v q.1, dT X l (u q.1), dTb X l (u q.1), dT X l (v q.1), dTb X l (v q.1)] q.2
  have hΦs : ∀ q, SlDom μ l c (Φs q) := by
    rintro ⟨a, j⟩
    fin_cases j
    · simpa [Φs, wOp_nil] using (hu a).2 []
    · simpa [Φs, wOp_nil] using (hv a).2 []
    · simpa [Φs, wOp_dT] using (hu a).2 [2, 0]
    · simpa [Φs, wOp_dTb] using (hu a).2 [5, 3]
    · simpa [Φs, wOp_dT] using (hv a).2 [2, 0]
    · simpa [Φs, wOp_dTb] using (hv a).2 [5, 3]
  obtain ⟨ε0, hε0, F, hF, hb⟩ := slDom_fin μ l c Φs hΦs t ht
  have hF0 : ∀ c', 0 ≤ F c' := fun c' =>
    (norm_nonneg _).trans (hb t (Metric.mem_ball_self hε0) c' (Classical.arbitrary _))

  have lu : ∀ a, u a ∈ lcSub k r z z' π π' := fun a => (hu a).1
  have lv : ∀ a, v a ∈ lcSub k r z z' π π' := fun a => (hv a).1

  have Iu : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (u a)) (Function.update c l s) :=
    fun a js s hs => level_l2_of_slice_domination μ l c ((hu a).2 js) hs
  have Iv : ∀ a (js : List (Fin 6)) s, s ≠ 0 → LevelSquareIntegrable μ l.succ (wOp X l js (v a)) (Function.update c l s) :=
    fun a js s hs => level_l2_of_slice_domination μ l c ((hv a).2 js) hs
  have I0u : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (u a) (Function.update c l s) := fun a s hs => by
    simpa [wOp_nil] using Iu a [] s hs
  have I0v : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (v a) (Function.update c l s) := fun a s hs => by
    simpa [wOp_nil] using Iv a [] s hs
  have ITu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (u a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dT] using Iu a [2, 0] s hs
  have ITv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dT X l (v a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dT] using Iv a [2, 0] s hs
  have IBu : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (u a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dTb] using Iu a [5, 3] s hs
  have IBv : ∀ a s, s ≠ 0 → LevelSquareIntegrable μ l.succ (dTb X l (v a)) (Function.update c l s) := fun a s hs => by
    simpa [wOp_dTb] using Iv a [5, 3] s hs

  set A : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' =>
    pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c') +
      pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c') with hA
  set Bf : Ix S → ℂ → Cf r l.succ → ℂ := fun a s c' =>
    pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c') +
      pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c') with hB
  set F0 : ℂ → Cf r l.succ → ℂ := fun s c' =>
    wtI l.succ c' * ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c') with hF0def
  set F' : ℂ → Cf r l.succ → (ℂ →L[ℝ] ℂ) := fun s c' =>
    wl (wtI l.succ c' * ∑ a, A a s c') (wtI l.succ c' * ∑ a, Bf a s c') with hF'def
  have hε : 0 < min ε0 ‖t‖ := lt_min hε0 (norm_pos_iff.mpr ht)
  have hne : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ≠ 0 := by
    intro s hs h0
    rw [h0, Metric.mem_ball, dist_zero_left] at hs
    exact (lt_irrefl _ (hs.trans_le (min_le_right _ _)))
  have hball : ∀ s ∈ Metric.ball t (min ε0 ‖t‖), s ∈ Metric.ball t ε0 := fun s hs =>
    Metric.ball_subset_ball (min_le_left _ _) hs

  have intF0 : ∀ s, s ≠ 0 → Integrable (F0 s) :=
    fun s hs => formIntOuter_of_l2I μ hμ l.succ u v lu lv (Function.update c l s) (fun a => I0u a s hs)
      (fun a => I0v a s hs)
  have hA1 := formIntOuter_of_l2I μ hμ l.succ (fun a => dT X l (u a)) v (fun a => dT_lc_OuterLeib X l (lu a)) lv
    (Function.update c l t) (fun a => ITu a t ht) (fun a => I0v a t ht)
  have hA2 := formIntOuter_of_l2I μ hμ l.succ u (fun a => dTb X l (v a)) lu (fun a => dTb_lc_OuterLeib X l (lv a))
    (Function.update c l t) (fun a => I0u a t ht) (fun a => IBv a t ht)
  have hB1 := formIntOuter_of_l2I μ hμ l.succ (fun a => dTb X l (u a)) v (fun a => dTb_lc_OuterLeib X l (lu a)) lv
    (Function.update c l t) (fun a => IBu a t ht) (fun a => I0v a t ht)
  have hB2 := formIntOuter_of_l2I μ hμ l.succ u (fun a => dT X l (v a)) lu (fun a => dT_lc_OuterLeib X l (lv a))
    (Function.update c l t) (fun a => I0u a t ht) (fun a => ITv a t ht)
  have intA : Integrable (fun c' => wtI l.succ c' * ∑ a, A a t c') := by
    refine (hA1.add hA2).congr (Eventually.of_forall fun c' => ?_)
    simp only [hA, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]
  have intB : Integrable (fun c' => wtI l.succ c' * ∑ a, Bf a t c') := by
    refine (hB1.add hB2).congr (Eventually.of_forall fun c' => ?_)
    simp only [hB, Pi.add_apply, Finset.sum_add_distrib, mul_add, wtI]
  have hIA : ∫ c', wtI l.succ c' * ∑ a, A a t c' =
      form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
        form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t) := by
    unfold form
    rw [← integral_add hA1 hA2]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only [hA, Finset.sum_add_distrib, mul_add, wtI]
  have hIB : ∫ c', wtI l.succ c' * ∑ a, Bf a t c' =
      form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
        form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t) := by
    unfold form
    rw [← integral_add hB1 hB2]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only [hB, Finset.sum_add_distrib, mul_add, wtI]
  have key : HasFDerivAt (fun s => ∫ c', F0 s c') (∫ c', F' t c') t := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun c' => 8 * (Fintype.card (Ix S) : ℝ) * F c') (Metric.ball_mem_nhds t hε) ?_ (intF0 t ht)
      (aesm_wl intA.aestronglyMeasurable intB.aestronglyMeasurable) ?_ (hF.const_mul _) ?_
    · exact Filter.eventually_of_mem (Metric.ball_mem_nhds t hε) fun s hs =>
        (intF0 s (hne s hs)).aestronglyMeasurable
    · refine Eventually.of_forall fun c' s hs => ?_
      have hs' := hball s hs
      have hd : ∀ a j, ‖wtI l.succ c' * pairAt μ (Φs (a, j)) (Φs (a, j)) (glue l.succ (Function.update c l s) c')‖
          ≤ F c' := fun a j => hb s hs' c' (a, j)
      have hAa : ∀ a, ‖wtI l.succ c' * A a s c'‖ ≤ 4 * F c' := by
        intro a
        have e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 0
        have e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 1
        have e2 : ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (dT X l (u a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 2
        have e5 : ‖wtI l.succ c' * pairAt μ (dTb X l (v a)) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 5
        have p1 := norm_wpair_le μ hμ (dT_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have p2 := norm_wpair_le μ hμ (lu a) (dTb_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have : ‖wtI l.succ c' * A a s c'‖ ≤
            ‖wtI l.succ c' * pairAt μ (dT X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ +
            ‖wtI l.succ c' * pairAt μ (u a) (dTb X l (v a)) (glue l.succ (Function.update c l s) c')‖ := by
          simp only [hA, mul_add]; exact norm_add_le _ _
        linarith
      have hBa : ∀ a, ‖wtI l.succ c' * Bf a s c'‖ ≤ 4 * F c' := by
        intro a
        have e0 : ‖wtI l.succ c' * pairAt μ (u a) (u a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 0
        have e1 : ‖wtI l.succ c' * pairAt μ (v a) (v a) (glue l.succ (Function.update c l s) c')‖ ≤ F c' := hd a 1
        have e3 : ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (dTb X l (u a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 3
        have e4 : ‖wtI l.succ c' * pairAt μ (dT X l (v a)) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖
            ≤ F c' := hd a 4
        have p1 := norm_wpair_le μ hμ (dTb_lc_OuterLeib X l (lu a)) (lv a) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have p2 := norm_wpair_le μ hμ (lu a) (dT_lc_OuterLeib X l (lv a)) (wtI l.succ c') (glue l.succ (Function.update c l s) c')
        have : ‖wtI l.succ c' * Bf a s c'‖ ≤
            ‖wtI l.succ c' * pairAt μ (dTb X l (u a)) (v a) (glue l.succ (Function.update c l s) c')‖ +
            ‖wtI l.succ c' * pairAt μ (u a) (dT X l (v a)) (glue l.succ (Function.update c l s) c')‖ := by
          simp only [hB, mul_add]; exact norm_add_le _ _
        linarith
      have sA : ‖wtI l.succ c' * ∑ a, A a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hAa a).trans ?_)
        simp
      have sB : ‖wtI l.succ c' * ∑ a, Bf a s c'‖ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hBa a).trans ?_)
        simp
      calc ‖F' s c'‖ ≤ ‖wtI l.succ c' * ∑ a, A a s c'‖ + ‖wtI l.succ c' * ∑ a, Bf a s c'‖ := norm_wl_le _ _
        _ ≤ (Fintype.card (Ix S) : ℝ) * (4 * F c') + (Fintype.card (Ix S) : ℝ) * (4 * F c') := add_le_add sA sB
        _ = 8 * (Fintype.card (Ix S) : ℝ) * F c' := by ring
    · refine Eventually.of_forall fun c' s hs => ?_
      have hd : ∀ a ∈ (Finset.univ : Finset (Ix S)),
          HasFDerivAt (fun s => pairAt μ (u a) (v a) (glue l.succ (Function.update c l s) c'))
            (wl (A a s c') (Bf a s c')) s :=
        fun a _ => hP k r z z' Wp Wq π π' X μ hμ l (u a) (v a) (lu a) (lv a) c hc c' s (hne s hs)
      have hs2 := (HasFDerivAt.sum hd).const_mul (wtI l.succ c')
      have e1 : (fun x => F0 x c') = fun y => wtI l.succ c' *
          (∑ i, fun s => pairAt μ (u i) (v i) (glue l.succ (Function.update c l s) c')) y := by
        funext y
        simp only [hF0def, Finset.sum_apply]
      have e2 : F' s c' = wtI l.succ c' • ∑ i, wl (A i s c') (Bf i s c') := by
        refine ContinuousLinearMap.ext fun h => ?_
        simp only [hF'def, wl_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
          smul_eq_mul]
        have alg : ∀ (f g : Ix S → ℂ) (w h : ℂ), w * (∑ a, f a) * h + w * (∑ a, g a) * conj h =
            w * ∑ a, (f a * h + g a * conj h) := by
          intro f g w h
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
        exact alg (fun a => A a s c') (fun a => Bf a s c') _ _
      rw [e1, e2]
      exact hs2
  have hfin : ∫ c', F' t c' =
      wl (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
            form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
        (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
            form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t)) := by
    rw [← hIA, ← hIB]
    exact integral_wl intA intB
  rw [hfin] at key
  exact key

end Formalism.FourierDecayAlt.P.CutSE
