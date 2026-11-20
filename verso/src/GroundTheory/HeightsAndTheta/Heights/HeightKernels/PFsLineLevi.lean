import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace FubiniStudyLeviForm

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩`. Consider the case `insert a s ha ih`. Establish `heq : (fun y => ∑ k ∈ insert a s, f k y) = fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y`. Use function extensionality and compare the values at `y`.

Rewrite using `[Finset.sum_insert ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]`.

Establish `h1` using `hl a w`. Establish `h2` using `ih.2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levi_sum_nonneg {K : Type} {z : ι → ℂ} (f : K → (ι → ℂ) → ℝ)
    (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (hl : ∀ k w, 0 ≤ ReciprocityTheory.AnForm.levi (f k) z w)
    (w : ι → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, f k y) z ∧
      0 ≤ ReciprocityTheory.AnForm.levi (fun y => ∑ k ∈ s, f k y) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, by simp [ReciprocityTheory.AnForm.levi]⟩
  | insert a s ha ih =>
    have heq : (fun y => ∑ k ∈ insert a s, f k y) =
        fun y => (fun y' => ∑ k ∈ s, f k y') y + 1 * f a y := by
      funext y
      rw [Finset.sum_insert ha]
      ring
    rw [heq]
    refine ⟨ih.1.add (contDiffAt_const.mul (hf a)), ?_⟩
    rw [ReciprocityTheory.AnForm.levi_add_smul (f := fun y' => ∑ k ∈ s, f k y') (g := f a) 1 ih.1 (hf a) w]
    have h1 := hl a w
    have h2 := ih.2
    linarith

noncomputable def blockProj {K : Type} (ι : K → Type) (k : K) : ((Σ k, ι k) → ℂ) →L[ℂ] (ι k → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨k, i⟩

end FubiniStudyLeviForm

open FubiniStudyLeviForm in

/- English proof (translation)
Introduce `K _ ι _ z w hz`. Use `set F : K → ((Σ k, ι k) → ℂ) → ℝ := fun k y => Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)) with hF`. Establish `hev : (fun y => Real.log ((fsMulti ι).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y`. Establish `hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hz k`.

Conclude with `Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi) fun y hy => ⟨i, hy⟩`. Use `filter_upwards [Filter.eventually_all.mpr hopen] with y hy`. Establish `hpos : ∀ k, 0 < (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)` using `fun k => by`. Take `⟨i, hi⟩` from `hy k`. Conclude with `(fsMetric (ι k)).pos _ fun h0 => hi (congrFun h0 i)`.

Simplify using `only [fsMulti, HermLine.ofMetrics, zpow_one, hF]`. Conclude with `Real.log_prod fun k _ => (hpos k).ne'`. Establish `hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v`. Introduce `k`. Establish `hk0 : (fun i => z ⟨k, i⟩) ≠ 0`.

Take `⟨i, hi⟩` from `hz k`. Conclude with `fun h0 => hi (congrFun h0 i)`. Establish `hφ` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0`. Establish `hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blockProj ι k` using `rfl`. Use `⟨hFk ▸ hφ.comp z ((blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj ι k).analyticAt z) hφ]`. Conclude with `HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _`. Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi _ z w`. Rewrite using `[ReciprocityTheory.AnForm.levi_congr hev]`. Conclude with `(levi_sum_nonneg F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2`.
-/
theorem FsLineLevi.proof : FsLineLevi.Statement := by
  intro K _ ι _ z w hz
  classical
  set F : K → ((Σ k, ι k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti ι).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric (ι k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hblock : ∀ k, ContDiffAt ℝ 2 (F k) z ∧ ∀ v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := by
    intro k
    have hk0 : (fun i => z ⟨k, i⟩) ≠ 0 := by
      obtain ⟨i, hi⟩ := hz k
      exact fun h0 => hi (congrFun h0 i)
    have hφ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_contDiffAt_logρ_id
      (HilbertSamuel.ProjLine.isSmoothMetric_fs (J := ι k)) hk0
    have hFk : F k = (fun u => Real.log ((fsMetric (ι k)).ρ u)) ∘ blockProj ι k := rfl
    refine ⟨hFk ▸ hφ.comp z ((blockProj ι k).restrictScalars ℝ).contDiff.contDiffAt, fun v => ?_⟩
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj ι k).analyticAt z) hφ]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg hk0 _
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  exact (levi_sum_nonneg F (fun k => (hblock k).1) (fun k => (hblock k).2) w Finset.univ).2

end GroundTheory.Heights₂.Heights
