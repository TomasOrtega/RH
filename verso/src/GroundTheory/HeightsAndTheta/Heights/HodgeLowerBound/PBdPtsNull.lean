import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsParamImageNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D`. Use `h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1) (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0}) (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_ (fun a => (D.chart a).analy …` and prove the remaining obligations. Introduce `a`. Use `measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_ (measure_iUnion_null fun i => ?_)` and prove the remaining obligations. Introduce and unpack `t ⟨-, i, -, hi⟩`.

Conclude with `Set.mem_iUnion.2 ⟨i, hi⟩`. Rewrite using `[volume_pi]`. Conclude with `Measure.pi_hyperplane _ i 0`. Introduce and unpack `z ⟨hz, -⟩`. Take `⟨a, t, ht, c, hc, rfl⟩` from `D.chart_cover z (D.bd_subset hz)`.

Establish `htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1` using `mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))`. Establish `hγ : (D.chart a).γ t ∈ D.Bd`. Establish `h'` using `D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))`. Use `h' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`.

Simplify using `[torusSmul, hc p.1]`. Conclude with `⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩`.
-/
theorem BdPtsNull.proof (h : ParamImageNull.Statement) : BdPtsNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  refine h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1)
    (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0})
    (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_
    (fun a => (D.chart a).analytic) ?_
  · intro a
    refine measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_
      (measure_iUnion_null fun i => ?_)
    · rintro t ⟨-, i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · rw [volume_pi]
      exact Measure.pi_hyperplane _ i 0
  · rintro z ⟨hz, -⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z (D.bd_subset hz)
    have htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))
    have hγ : (D.chart a).γ t ∈ D.Bd := by
      have h' := D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))
      convert h' using 1
      funext p
      simp [torusSmul, hc p.1]
    exact ⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
