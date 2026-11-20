import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramLocTendsto
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoLevelNormOfRegularization

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `E _ _ _ Wp Wq _ _ _ _ S RR hg1 hg2 hU hconv hInt hB`. Establish `hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 → D.ptSize h' = i - 1 → ∃ M : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 → ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ M * ((1 + ‖c‖) ^ 3)⁻¹`. Introduce `v ε hε i hi1 hi2 a ha h h' hh hh'`. Take `⟨M, hM⟩` from `hB v ε hε i hi1 hi2 a ha h h' hh hh'`. Conclude with `⟨M, fun n => (hM n).1⟩`.

Use `⟨PBB.K8.intAll_limit S RR hg1 hg2 hconv hInt hB, ?_⟩` and prove the remaining obligations. Introduce `X hX ε hε i hi1 hi2 w hw hcnt`. Use `set B := S.base.Wb (S.base.cnt w + C.Kst) with hBdef`. Establish `hθ : ∀ n, ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb B (θ A)) ∧ ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ → ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f), (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR n)).Nhat ε i w.1 Y κ l‖ ≤ (∏ …` using `fun n => hX n ε hε i hi1 hi2 w hw hcnt`. Use `choose θ hprob hineq using hθ`.

Set `F : ℕ → (Finset (Fin S.f) → B → ℝ)` to `fun n A x => θ n A x.1`. Establish `hFb : ∀ n, F n ∈ Metric.closedBall (0 : Finset (Fin S.f) → B → ℝ) 1`. Introduce `n`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `A`.

Rewrite using `[pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `x`. Establish `h0` using `(hprob n A).1 x.1`. Use `show ‖θ n A x.1‖ ≤ 1`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg h0]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨a, -, φ, hφ, hlim⟩` from `tendsto_subseq_of_bounded Metric.isBounded_closedBall hFb`. Establish `hco : ∀ A (x : B), Filter.Tendsto (fun n => θ (φ n) A x.1) Filter.atTop (nhds (a A x))`. Introduce `A x`. Conclude with `((continuous_apply x).comp (continuous_apply A)).tendsto a |>.comp hlim`.

Set `θ' : Finset (Fin S.f) → S.W → ℝ` to `fun A w' => if h : w' ∈ B then a A ⟨w', h⟩ else 0`. Establish `hθ' : ∀ A w' (h : w' ∈ B), θ' A w' = a A ⟨w', h⟩` using `fun A w' h => dif_pos h`. Use `⟨θ', ?_, ?_⟩` and prove the remaining obligations. Introduce `A`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `w'`. Distinguish the cases in `h : w' ∈ B`. Rewrite using `[hθ' A w' h]`. Conclude with `ge_of_tendsto' (hco A ⟨w', h⟩) fun n => (hprob (φ n) A).1 w'`. Use `show 0 ≤ (if h : w' ∈ B then a A ⟨w', h⟩ else 0)`.

Rewrite using `[dif_neg h]`. Introduce `w' h show (if h : w' ∈ B then a A ⟨w', h⟩ else 0) = 0`. Rewrite using `[dif_neg h]`. Establish `e1 : ∑ w' ∈ B, θ' A w' = ∑ x : B, a A x`. Rewrite using `[← Finset.sum_coe_sort B]`.

Conclude with `Finset.sum_congr rfl fun x _ => hθ' A x.1 x.2`. Establish `e2 : ∀ n, ∑ x : B, θ (φ n) A x.1 = 1` using `fun n => by`. Rewrite using `[Finset.sum_coe_sort B (θ (φ n) A)]`. Conclude with `(hprob (φ n) A).2.2`. Rewrite using `[e1]`.

Use `tendsto_nhds_unique (tendsto_finset_sum _ fun x _ => hco A x) ?_` and prove the remaining obligations. Repeatedly rewrite using `[e2]`. Conclude with `tendsto_const_nhds`. Introduce `Y hY κ hκ l hl hl0 A`. Establish `hL : Filter.Tendsto (fun n => (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR (φ n))).Nhat ε i w.1 Y κ l‖) Filter.atTop (nhds ((∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖))` using `(((PBB.tendsto_Nhat S RR hconv hInt hbd ε hε i hi1 hi2 w Y hY κ l).comp hφ.tendsto_atTop).norm).const_mul _`.

Establish `hR : Filter.Tendsto (fun n => (∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ (φ n) A w' * (KB.withRR S (RR (φ n))).base.N0 ε (i - 1) w' Y κ) Filter.atTop (nhds ((∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ' A w' * S.base.N0 ε (i - 1) w' Y κ))`. Use `Filter.Tendsto.const_mul _ (tendsto_finset_sum _ fun w' hw' => ?_)` and prove the remaining obligations. Use `Filter.Tendsto.mul ?_ ((PBB.tendsto_base_norm_of_regularization S RR hconv ε hε (i - 1) (by omega) w' Y κ).comp hφ.tendsto_atTop)` and prove the remaining obligations. Rewrite using `[hθ' A w' hw']`. Conclude with `hco A ⟨w', hw'⟩`.

Conclude with `le_of_tendsto_of_tendsto' hL hR fun n => hineq (φ n) Y hY κ hκ l hl hl0 A`.
-/
theorem integral_formula_passes_to_limits : Formalism.FourierDecayAlt.KB.LimitInt := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hg1 hg2 hU hconv hInt hB
  have hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h',
      D.ptSize h = i - 1 → D.ptSize h' = i - 1 → ∃ M : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ M * ((1 + ‖c‖) ^ 3)⁻¹ := by
    intro v ε hε i hi1 hi2 a ha h h' hh hh'
    obtain ⟨M, hM⟩ := hB v ε hε i hi1 hi2 a ha h h' hh hh'
    exact ⟨M, fun n => (hM n).1⟩
  refine ⟨PBB.K8.intAll_limit S RR hg1 hg2 hconv hInt hB, ?_⟩
  intro X hX ε hε i hi1 hi2 w hw hcnt
  set B := S.base.Wb (S.base.cnt w + C.Kst) with hBdef
  have hθ : ∀ n, ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb B (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖(KB.withRR S (RR n)).Nhat ε i w.1 Y κ l‖ ≤
            (∏ v ∈ A, X i v ^ C.Kst) *
              ∑ w' ∈ B, θ A w' * (KB.withRR S (RR n)).base.N0 ε (i - 1) w' Y κ :=
    fun n => hX n ε hε i hi1 hi2 w hw hcnt
  choose θ hprob hineq using hθ

  let F : ℕ → (Finset (Fin S.f) → B → ℝ) := fun n A x => θ n A x.1
  have hFb : ∀ n, F n ∈ Metric.closedBall (0 : Finset (Fin S.f) → B → ℝ) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro A
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    have h0 := (hprob n A).1 x.1
    show ‖θ n A x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc θ n A x.1 ≤ ∑ w' ∈ B, θ n A w' :=
          Finset.single_le_sum (fun w' _ => (hprob n A).1 w') x.2
      _ = 1 := (hprob n A).2.2
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hFb
  have hco : ∀ A (x : B), Filter.Tendsto (fun n => θ (φ n) A x.1) Filter.atTop (nhds (a A x)) := by
    intro A x
    exact ((continuous_apply x).comp (continuous_apply A)).tendsto a |>.comp hlim
  let θ' : Finset (Fin S.f) → S.W → ℝ := fun A w' => if h : w' ∈ B then a A ⟨w', h⟩ else 0
  have hθ' : ∀ A w' (h : w' ∈ B), θ' A w' = a A ⟨w', h⟩ := fun A w' h => dif_pos h
  refine ⟨θ', ?_, ?_⟩
  · intro A
    refine ⟨?_, ?_, ?_⟩
    · intro w'
      by_cases h : w' ∈ B
      · rw [hθ' A w' h]
        exact ge_of_tendsto' (hco A ⟨w', h⟩) fun n => (hprob (φ n) A).1 w'
      · show 0 ≤ (if h : w' ∈ B then a A ⟨w', h⟩ else 0)
        rw [dif_neg h]
    · intro w' h
      show (if h : w' ∈ B then a A ⟨w', h⟩ else 0) = 0
      rw [dif_neg h]
    · have e1 : ∑ w' ∈ B, θ' A w' = ∑ x : B, a A x := by
        rw [← Finset.sum_coe_sort B]
        exact Finset.sum_congr rfl fun x _ => hθ' A x.1 x.2
      have e2 : ∀ n, ∑ x : B, θ (φ n) A x.1 = 1 := fun n => by
        rw [Finset.sum_coe_sort B (θ (φ n) A)]
        exact (hprob (φ n) A).2.2
      rw [e1]
      refine tendsto_nhds_unique (tendsto_finset_sum _ fun x _ => hco A x) ?_
      simp_rw [e2]
      exact tendsto_const_nhds
  · intro Y hY κ hκ l hl hl0 A
    have hL : Filter.Tendsto (fun n => (∏ v ∈ A, S.base.av v l ^ C.Kst) *
        ‖(KB.withRR S (RR (φ n))).Nhat ε i w.1 Y κ l‖) Filter.atTop
        (nhds ((∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖)) :=
      (((PBB.tendsto_Nhat S RR hconv hInt hbd ε hε i hi1 hi2 w Y hY κ l).comp
        hφ.tendsto_atTop).norm).const_mul _
    have hR : Filter.Tendsto (fun n => (∏ v ∈ A, X i v ^ C.Kst) *
        ∑ w' ∈ B, θ (φ n) A w' * (KB.withRR S (RR (φ n))).base.N0 ε (i - 1) w' Y κ) Filter.atTop
        (nhds ((∏ v ∈ A, X i v ^ C.Kst) * ∑ w' ∈ B, θ' A w' * S.base.N0 ε (i - 1) w' Y κ)) := by
      refine Filter.Tendsto.const_mul _ (tendsto_finset_sum _ fun w' hw' => ?_)
      refine Filter.Tendsto.mul ?_ ((PBB.tendsto_base_norm_of_regularization S RR hconv ε hε (i - 1) (by omega) w' Y κ).comp
        hφ.tendsto_atTop)
      rw [hθ' A w' hw']
      exact hco A ⟨w', hw'⟩
    exact le_of_tendsto_of_tendsto' hL hR fun n => hineq (φ n) Y hY κ hκ l hl hl0 A

end Formalism.FourierDecayAlt.P
