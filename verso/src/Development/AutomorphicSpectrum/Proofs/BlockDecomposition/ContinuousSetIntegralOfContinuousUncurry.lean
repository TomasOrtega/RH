import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorantStatement
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1Theta

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j ↦ ?_ fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Function.comp_def, scal, borelElt_val] <;> first | exact Units.continuous_val | exact continuous_const`. Establish `hinv : Continuous fun a : IdeleGroup K ↦ ((a⁻¹ : IdeleGroup K) : 𝔸[K])` using `Units.continuous_val.comp continuous_inv`. Use `continuous_matrix fun i j ↦ ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `hinv`. Simplify `continuous_const` using `[scal, borelElt]`. Simplify `continuous_const` using `[scal, borelElt]`. Conclude with `hinv`.
-/
theorem continuous_scal : Continuous (scal : IdeleGroup K → GL (Fin 2) 𝔸[K]) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp [Function.comp_def, scal, borelElt_val] <;> first | exact Units.continuous_val | exact continuous_const
  · have hinv : Continuous fun a : IdeleGroup K ↦ ((a⁻¹ : IdeleGroup K) : 𝔸[K]) :=
      Units.continuous_val.comp continuous_inv
    refine continuous_matrix fun i j ↦ ?_
    fin_cases i <;> fin_cases j
    · exact hinv
    · simpa [scal, borelElt] using continuous_const
    · simpa [scal, borelElt] using continuous_const
    · exact hinv

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun h₀ ↦ ?_` and prove the remaining obligations. Take `⟨C, hC, hh₀⟩` from `exists_compact_mem_nhds h₀`. Take `⟨u, hu, hFu⟩` from `GlobalTheory.T.schwartz_bruhat_uniform_summable_majorant hF hC`. Establish `hcont : ContinuousOn (theta2 F) C`. Use `continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ` and prove the remaining obligations.

Use `(continuous_of_mem_schwartzBruhat2 hF).comp ?_` and prove the remaining obligations. Conclude with `continuous_const.matrix_vecMul Units.continuous_val`. Conclude with `hcont.continuousAt hh₀`.
-/
theorem continuous_theta2 {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) :
    Continuous (theta2 F) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.schwartz_bruhat_uniform_summable_majorant hF hC
  have hcont : ContinuousOn (theta2 F) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhat2 hF).comp ?_
    exact continuous_const.matrix_vecMul Units.continuous_val
  exact hcont.continuousAt hh₀

/- English proof (translation)
Establish `hint : ∀ x, IntegrableOn (f x) E ν` using `fun x ↦ by`. Establish `hc : Continuous (f x)` using `hf.comp (Continuous.prodMk_right x)`. Conclude with `(hc.continuousOn.integrableOn_compact hE).mono_set subset_closure`. Use `continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_` and prove the remaining obligations. Use `set m := ν.real E with hm`.

Establish `hm0 : 0 ≤ m` using `measureReal_nonneg`. Establish `hδ : 0 < ε / (2 * (m + 1))` using `by positivity`. Take `⟨v, hv, hvu⟩` from `hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q) hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)`. Rewrite `hv` using `[nhdsWithin_univ]`. Use `filter_upwards [hv] with p hp`.

Rewrite using `[dist_eq_norm, ← integral_sub (hint p) (hint q)]`. Establish `hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m`. Use `norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_` and prove the remaining obligations. Use `hvu p hp u (subset_closure hu)` as an intermediate fact. Rewrite `this` using `[Set.mem_setOf_eq, dist_eq_norm]`.

Conclude with `this.le`. Use `hb.trans_lt ?_` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem continuous_setIntegral_of_continuous_uncurry {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y)
    [IsFiniteMeasureOnCompacts ν] {E : Set Y} (hE : IsCompact (closure E)) (hν : ν E < ⊤)
    {f : X → Y → ℂ} (hf : Continuous (Function.uncurry f)) :
    Continuous fun x ↦ ∫ u in E, f x u ∂ν := by
  have hint : ∀ x, IntegrableOn (f x) E ν := fun x ↦ by
    have hc : Continuous (f x) := hf.comp (Continuous.prodMk_right x)
    exact (hc.continuousOn.integrableOn_compact hE).mono_set subset_closure
  refine continuous_iff_continuousAt.2 fun q ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  set m := ν.real E with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hδ : 0 < ε / (2 * (m + 1)) := by positivity
  obtain ⟨v, hv, hvu⟩ := hE.mem_uniformity_of_prod (f := f) (s := Set.univ) (q := q)
    hf.continuousOn (Set.mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with p hp
  rw [dist_eq_norm, ← integral_sub (hint p) (hint q)]
  have hb : ‖∫ u in E, (f p u - f q u) ∂ν‖ ≤ ε / (2 * (m + 1)) * m := by
    refine norm_setIntegral_le_of_norm_le_const hν fun u hu ↦ ?_
    have := hvu p hp u (subset_closure hu)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine hb.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

noncomputable def translatedIntegrand (w : InfinitePlace K) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (μ : HeckeCharacter K) (p : {r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) (u : normOneSubgroup K) : ℂ :=
  theta2 Φ (scal (moduleSection w p.1 * (u : IdeleGroup K)) * p.2) *
    (μ.toIdele (u : IdeleGroup K) : ℂ)

/- English proof (translation)
Establish `hu : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦ (x.2 : IdeleGroup K)` using `continuous_subtype_val.comp continuous_snd`. Establish `hs : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦ moduleSection w x.1.1` using `(continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)`. Establish `hg : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦ x.1.2` using `continuous_snd.comp continuous_fst`. Conclude with `((continuous_theta2 hΦ).comp ((continuous_scal.comp (hs.mul hu)).mul hg)).mul (continuous_subtype_val.comp (μ.continuous_toIdele.comp hu))`.
-/
theorem continuous_translatedIntegrand (w : InfinitePlace K) {Φ : (Fin 2 → 𝔸[K]) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 K) (μ : HeckeCharacter K) :
    Continuous (Function.uncurry (translatedIntegrand w Φ μ)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      (x.2 : IdeleGroup K) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL (Fin 2) 𝔸[K]) × normOneSubgroup K ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_theta2 hΦ).comp ((continuous_scal.comp (hs.mul hu)).mul hg)).mul
    (continuous_subtype_val.comp (μ.continuous_toIdele.comp hu))

end GlobalTheory.CompanionTheory.EisRk1Theta
