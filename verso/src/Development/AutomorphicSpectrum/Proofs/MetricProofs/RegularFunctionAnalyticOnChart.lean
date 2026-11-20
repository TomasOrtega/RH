import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtHolomorphicComposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

/- English proof (translation)
Introduce `K _ ι _ Ω _ x s e n Rb Un bp w₀ hUn hw₀ hbp hchart hreg`. Take `⟨W', hW'o, hx₀W', hW'U, hW'holo⟩` from `GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_valAt K ι Ω x s n Rb.X Rb.A (Rb.U (bp w₀)) (Rb.lift (bp w₀)) (bp w₀) (Rb.isOpen_U _) (Rb.mem_U _) (fun q => Rb.holo _ q) (fun y hy => Rb.mem _ y hy) hreg`. Take `⟨j, hj⟩` from `Rb.A.cover (bp w₀)`. Establish `hg : AnalyticAt ℂ ((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ((Rb.A.chart j) (bp w₀))`. Apply `hW'holo j` to reduce the goal to its premises.

Use `⟨(Rb.A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (Rb.A.chart j).symm ((Rb.A.chart j) (bp w₀)) ∈ W'`. Rewrite using `[(Rb.A.chart j).left_inv hj]`. Conclude with `hx₀W'`. Establish `hf : AnalyticAt ℂ ((Rb.A.chart j) ∘ bp) w₀` using `hchart j w₀ ⟨hw₀, hj⟩`.

Establish `hcomp : AnalyticAt ℂ (((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ∘ ((Rb.A.chart j) ∘ bp)) w₀` using `AnalyticAt.comp_of_eq (g := (fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) (f := (Rb.A.chart j) ∘ bp) hg hf rfl`. Use `hcomp.congr ?_` and prove the remaining obligations. Establish `hcont : ContinuousAt bp w₀` using `hbp.continuousAt (hUn.mem_nhds hw₀)`. Establish `hnhds : bp ⁻¹' ((Rb.A.chart j).source ∩ W') ∈ 𝓝 w₀` using `hcont.preimage_mem_nhds (((Rb.A.chart j).open_source.inter hW'o).mem_nhds ⟨hj, hx₀W'⟩)`. Use `filter_upwards [hnhds] with w hw`.

Take `⟨hws, hwW⟩` from `hw`. Use `show GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) ((Rb.A.chart j).symm ((Rb.A.chart j) (bp w)))) = GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w) (bp w))`. Rewrite using `[(Rb.A.chart j).left_inv hws]`. Conclude with `(GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit K ι Ω x s _ _ (Rb.mem _ _ (Rb.mem_U _)) (Rb.compat (bp w) (bp w₀) (bp w) ⟨Rb.mem_U _, hW'U hwW⟩)).symm`.
-/
theorem analyticAt_valAt_lift_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (e n : ℕ) (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → Rb.X) (w₀ : Fin e → ℂ), IsOpen Un → w₀ ∈ Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (Rb.A.chart k).source)) → RegAt x (mCoordIdeal (Rb.lift (bp w₀) (bp w₀))) s → AnalyticAt ℂ (fun w => valAt x s (Rb.lift (bp w) (bp w))) w₀ := by
  intro K _ ι _ Ω _ x s e n Rb Un bp w₀ hUn hw₀ hbp hchart hreg
  obtain ⟨W', hW'o, hx₀W', hW'U, hW'holo⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_valAt K ι Ω x s n Rb.X Rb.A (Rb.U (bp w₀))
      (Rb.lift (bp w₀)) (bp w₀) (Rb.isOpen_U _) (Rb.mem_U _) (fun q => Rb.holo _ q)
      (fun y hy => Rb.mem _ y hy) hreg
  obtain ⟨j, hj⟩ := Rb.A.cover (bp w₀)
  have hg : AnalyticAt ℂ ((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ((Rb.A.chart j) (bp w₀)) := by
    apply hW'holo j
    refine ⟨(Rb.A.chart j).map_source hj, ?_⟩
    show (Rb.A.chart j).symm ((Rb.A.chart j) (bp w₀)) ∈ W'
    rw [(Rb.A.chart j).left_inv hj]
    exact hx₀W'
  have hf : AnalyticAt ℂ ((Rb.A.chart j) ∘ bp) w₀ := hchart j w₀ ⟨hw₀, hj⟩
  have hcomp : AnalyticAt ℂ (((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ∘ ((Rb.A.chart j) ∘ bp)) w₀ :=
    AnalyticAt.comp_of_eq (g := (fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) (f := (Rb.A.chart j) ∘ bp) hg hf rfl
  refine hcomp.congr ?_
  have hcont : ContinuousAt bp w₀ := hbp.continuousAt (hUn.mem_nhds hw₀)
  have hnhds : bp ⁻¹' ((Rb.A.chart j).source ∩ W') ∈ 𝓝 w₀ :=
    hcont.preimage_mem_nhds (((Rb.A.chart j).open_source.inter hW'o).mem_nhds ⟨hj, hx₀W'⟩)
  filter_upwards [hnhds] with w hw
  obtain ⟨hws, hwW⟩ := hw
  show GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) ((Rb.A.chart j).symm ((Rb.A.chart j) (bp w)))) = GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w) (bp w))
  rw [(Rb.A.chart j).left_inv hws]
  exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit K ι Ω x s _ _ (Rb.mem _ _ (Rb.mem_U _))
    (Rb.compat (bp w) (bp w₀) (bp w) ⟨Rb.mem_U _, hW'U hwW⟩)).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
