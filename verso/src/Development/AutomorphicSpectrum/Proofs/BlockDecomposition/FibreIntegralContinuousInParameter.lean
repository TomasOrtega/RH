import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibreJointOpen

/- English proof (translation)
Introduce `V X Y _ _ _ _ _ _ _ _ μ ν f ι U hU B hB fib hF P _ W Φ hΦ hW C hC hCU hsupp`. Take `⟨-, -, h3⟩` from `hF`. Establish `hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v)` using `fun p hp v => hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)`. Establish `hslice : ∀ p ∈ W, Continuous (Φ p)` using `fun p hp => continuous_iff_continuousAt.2 fun v => ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2) (hAt p hp v) (by fun_prop)`. Establish `hcs : ∀ p ∈ W, HasCompactSupport (Φ p)` using `fun p hp => HasCompactSupport.intro hC (hsupp p hp)`.

Establish `hts : ∀ p ∈ W, tsupport (Φ p) ⊆ U` using `fun p hp => by`. Use `(closure_minimal ?_ hC.isClosed).trans hCU` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hvC`. Conclude with `hv (hsupp p hp v hvC)`.

Establish `hint : ∀ p ∈ W, ∀ b ∈ B, Integrable (Φ p) (fib b)` using `fun p hp b hb => (h3 (Φ p) (hslice p hp) (hcs p hp) (hts p hp)).1 b hb`. Establish `hbd : ∀ D : Set X, IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c`. Introduce `D hD hDB`. Take `⟨φ, hc, hcs', hs, h0, -, hone⟩` from `GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU`. Take `⟨hi, hco⟩` from `h3 φ hc hcs' hs`.

Take `⟨M, hM⟩` from `hD.exists_bound_of_continuousOn (hco.mono hDB)`. Use `⟨M.toNNReal, fun b hb => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩`. Simplify using `only [Set.mem_prod] at hp₀ hb₀ ⊢`.

Use `ContinuousAt.continuousWithinAt ?_` and prove the remaining obligations. Take `⟨D, hDn, hDB, hDc⟩` from `local_compact_nhds (hB.mem_nhds hb₀)`. Take `⟨c, hc⟩` from `hbd D hDc hDB`. Use `Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Use `set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ`.

Establish `hc0 : (0 : ℝ) ≤ c` using `c.2`. Establish `hδ0 : 0 < δ` using `by positivity`. Establish `htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ`. Use `hC.eventually_forall_of_forall_eventually fun v _ => ?_` and prove the remaining obligations. Establish `h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v)` using `(hAt p₀ hp₀ v).sub (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀) (hslice p₀ hp₀).continuousAt continuousAt_snd)`.

Establish `h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0)`. Establish `h3` using `h1.tendsto`. Simplify using `only [sub_self] at h3`. Conclude with `h3`. Establish `h4` using `(Metric.tendsto_nhds.1 h2) δ hδ0`.

Use `filter_upwards [h4] with z hz`. Simplify `hz` using `[Real.dist_eq]`. Establish `hb : ∀ᶠ b in 𝓝 b₀, |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2`. Establish `h1` using `(((h3 (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀) (hts p₀ hp₀)).2).continuousAt (hB.mem_nhds hb₀)).tendsto`. Establish `h2` using `(Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)`.

Use `filter_upwards [h2] with b hb`. Simplify `hb` using `[Real.dist_eq]`. Rewrite using `[nhds_prod_eq]`. Establish `hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ` using `Filter.Eventually.and (hW.mem_nhds hp₀) htube`. Establish `hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧ |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2` using `Filter.Eventually.and hDn hb`.

Use `filter_upwards [hp.prod_mk hbb] with q hq`. Take `⟨⟨hqW, hqt⟩, hqD, hqb⟩` from `hq`. Take `⟨p, b⟩` from `q`. Simplify using `only at hqW hqt hqD hqb ⊢`. Establish `hbB : b ∈ B` using `hDB hqD`.

Establish `hfin : fib b C < ∞` using `(hc b hqD).trans_lt ENNReal.coe_lt_top`. Establish `hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b) = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)`. Rewrite using `[← integral_sub (hint p hqW b hbB) (hint p₀ hp₀ b hbB)]`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm` and prove the remaining obligations. Rewrite using `[hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]`.

Establish `hreal : (fib b).real C ≤ c`. Use `ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)` as an intermediate fact. Simplify `this` using `[Measure.real]`. Establish `hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ)`. Rewrite using `[hdiff, ← Real.norm_eq_abs]`.

Establish `h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C` using `norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by`. Rewrite using `[Real.norm_eq_abs]`. Conclude with `(hqt v hv).le`. Conclude with `h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)`. Establish `hδc : δ * (c : ℝ) ≤ ε / 2`.

Rewrite using `[hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Real.dist_eq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem continuousOn_fibre_integral_of_subset : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V), IsOpen U → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib → ∀ (P : Type) [TopologicalSpace P] (W : Set P) (Φ : P → V → ℝ), ContinuousOn (fun p : P × V => Φ p.1 p.2) (W ×ˢ Set.univ) → IsOpen W → ∀ C : Set V, IsCompact C → C ⊆ U → (∀ p ∈ W, ∀ v, v ∉ C → Φ p v = 0) → ContinuousOn (fun q : P × X => ∫ v, Φ q.1 v ∂(fib q.2)) (W ×ˢ B) := by
  intro V X Y _ _ _ _ _ _ _ _ μ ν f ι U hU B hB fib hF P _ W Φ hΦ hW C hC hCU hsupp
  obtain ⟨-, -, h3⟩ := hF

  have hAt : ∀ p ∈ W, ∀ v, ContinuousAt (fun p : P × V => Φ p.1 p.2) (p, v) := fun p hp v =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ v⟩)
  have hslice : ∀ p ∈ W, Continuous (Φ p) := fun p hp =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (p, v)) (g := fun p : P × V => Φ p.1 p.2)
        (hAt p hp v) (by fun_prop)
  have hcs : ∀ p ∈ W, HasCompactSupport (Φ p) := fun p hp =>
    HasCompactSupport.intro hC (hsupp p hp)
  have hts : ∀ p ∈ W, tsupport (Φ p) ⊆ U := fun p hp => by
    refine (closure_minimal ?_ hC.isClosed).trans hCU
    intro v hv
    by_contra hvC
    exact hv (hsupp p hp v hvC)
  have hint : ∀ p ∈ W, ∀ b ∈ B, Integrable (Φ p) (fib b) := fun p hp b hb =>
    (h3 (Φ p) (hslice p hp) (hcs p hp) (hts p hp)).1 b hb

  have hbd : ∀ D : Set X, IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
    intro D hD hDB
    obtain ⟨φ, hc, hcs', hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs' hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono hDB)
    refine ⟨M.toNNReal, fun b hb => ?_⟩
    calc fib b C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(fib b)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi b (hDB hb))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM b hb))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  rintro ⟨p₀, b₀⟩ ⟨hp₀, hb₀⟩
  simp only [Set.mem_prod] at hp₀ hb₀ ⊢
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨D, hDn, hDB, hDc⟩ := local_compact_nhds (hB.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hbd D hDc hDB
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set δ : ℝ := ε / (2 * ((c : ℝ) + 1)) with hδ
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hδ0 : 0 < δ := by positivity

  have htube : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ := by
    refine hC.eventually_forall_of_forall_eventually fun v _ => ?_
    have h1 : ContinuousAt (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (p₀, v) :=
      (hAt p₀ hp₀ v).sub
        (ContinuousAt.comp (f := fun z : P × V => z.2) (g := Φ p₀)
          (hslice p₀ hp₀).continuousAt continuousAt_snd)
    have h2 : Filter.Tendsto (fun z : P × V => Φ z.1 z.2 - Φ p₀ z.2) (𝓝 (p₀, v)) (𝓝 0) := by
      have h3 := h1.tendsto
      simp only [sub_self] at h3
      exact h3
    have h4 := (Metric.tendsto_nhds.1 h2) δ hδ0
    filter_upwards [h4] with z hz
    simpa [Real.dist_eq] using hz
  have hb : ∀ᶠ b in 𝓝 b₀,
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := by
    have h1 := (((h3 (Φ p₀) (hslice p₀ hp₀) (hcs p₀ hp₀) (hts p₀ hp₀)).2).continuousAt
      (hB.mem_nhds hb₀)).tendsto
    have h2 := (Metric.tendsto_nhds.1 h1) (ε / 2) (by positivity)
    filter_upwards [h2] with b hb
    simpa [Real.dist_eq] using hb
  rw [nhds_prod_eq]
  have hp : ∀ᶠ p in 𝓝 p₀, p ∈ W ∧ ∀ v ∈ C, |Φ p v - Φ p₀ v| < δ :=
    Filter.Eventually.and (hW.mem_nhds hp₀) htube
  have hbb : ∀ᶠ b in 𝓝 b₀, b ∈ D ∧
      |∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)| < ε / 2 := Filter.Eventually.and hDn hb
  filter_upwards [hp.prod_mk hbb] with q hq
  obtain ⟨⟨hqW, hqt⟩, hqD, hqb⟩ := hq
  obtain ⟨p, b⟩ := q
  simp only at hqW hqt hqD hqb ⊢
  have hbB : b ∈ B := hDB hqD
  have hfin : fib b C < ∞ := (hc b hqD).trans_lt ENNReal.coe_lt_top
  have hdiff : ∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)
      = ∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b) := by
    rw [← integral_sub (hint p hqW b hbB) (hint p₀ hp₀ b hbB)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [hsupp p hqW v hv, hsupp p₀ hp₀ v hv, sub_zero]
  have hreal : (fib b).real C ≤ c := by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hc b hqD)
    simpa [Measure.real] using this
  have hle : |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b)| ≤ δ * (c : ℝ) := by
    rw [hdiff, ← Real.norm_eq_abs]
    have h5 : ‖∫ v in C, (Φ p v - Φ p₀ v) ∂(fib b)‖ ≤ δ * (fib b).real C :=
      norm_setIntegral_le_of_norm_le_const (C := δ) hfin fun v hv => by
        rw [Real.norm_eq_abs]; exact (hqt v hv).le
    exact h5.trans (mul_le_mul_of_nonneg_left hreal hδ0.le)
  have hδc : δ * (c : ℝ) ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀)|
      = |(∫ v, Φ p v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b))
          + (∫ v, Φ p₀ v ∂(fib b) - ∫ v, Φ p₀ v ∂(fib b₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ < ε := by linarith

end GlobalTheory.CompanionTheory.SW.FibreJointOpen
