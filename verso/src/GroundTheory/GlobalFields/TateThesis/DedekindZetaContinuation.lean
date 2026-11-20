import Mathlib
import GroundTheory.GlobalFields.TateThesis.DedekindContinuation

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped Real

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

open HeckeCharacter

/- English proof (translation)
Establish `h` using `gammaFactor_neg_of_forall (one_toIdele_eq_cpow (K := K))`. Simplify using `only [ofReal_zero, zero_mul, neg_zero] at h`. Rewrite `h` using `[gammaFactor_one]`. Rewrite using `[h, inv_zero, mul_zero]`.
-/
theorem discr_cpow_mul_gamma_inv_zero :
    ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-((0 : ℂ) / 2)) *
      (Gammaℝ 0 ^ nrRealPlaces K * Gammaℂ 0 ^ nrComplexPlaces K)⁻¹ = 0 := by
  have h := gammaFactor_neg_of_forall (one_toIdele_eq_cpow (K := K))
  simp only [ofReal_zero, zero_mul, neg_zero] at h
  rw [gammaFactor_one] at h
  rw [h, inv_zero, mul_zero]

/- English proof (translation)
Use `set H : ℂ → ℂ := fun s ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) * (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ with hH`. Establish `hdiff : Differentiable ℂ H` using `differentiable_discr_cpow_mul_gamma_inv K`. Establish `hH0 : H 0 = 0` using `discr_cpow_mul_gamma_inv_zero K`. Establish `hslope : Tendsto (fun s ↦ s⁻¹ * H s) (𝓝[≠] 0) (𝓝 (deriv H 0))`. Use `(hasDerivAt_iff_tendsto_slope.1 (hdiff 0).hasDerivAt).congr fun s ↦ ?_` and prove the remaining obligations.

Rewrite using `[slope_fun_def_field, hH0]`. Use `beta_reduce`. Rewrite using `[sub_zero, sub_zero, div_eq_inv_mul]`. Use `⟨_, (hslope.mul (tendsto_mul_completedDedekindZeta_zero K)).congr' ?_⟩` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Establish `hs' : s ≠ 0` using `hs`. Simplify using `only [normalizedDedekindZeta, hH]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_tendsto_normalizedDedekindZeta_zero :
    ∃ L, Tendsto (normalizedDedekindZeta K) (𝓝[≠] 0) (𝓝 L) := by
  set H : ℂ → ℂ := fun s ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
    (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ with hH
  have hdiff : Differentiable ℂ H := differentiable_discr_cpow_mul_gamma_inv K
  have hH0 : H 0 = 0 := discr_cpow_mul_gamma_inv_zero K
  have hslope : Tendsto (fun s ↦ s⁻¹ * H s) (𝓝[≠] 0) (𝓝 (deriv H 0)) := by
    refine (hasDerivAt_iff_tendsto_slope.1 (hdiff 0).hasDerivAt).congr fun s ↦ ?_
    rw [slope_fun_def_field, hH0]
    beta_reduce
    rw [sub_zero, sub_zero, div_eq_inv_mul]
  refine ⟨_, (hslope.mul (tendsto_mul_completedDedekindZeta_zero K)).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ 0 := hs
  simp only [normalizedDedekindZeta, hH]
  field_simp

def continuedDedekindZeta : ℂ → ℂ :=
  Function.update (normalizedDedekindZeta K) 0 (limUnder (𝓝[≠] 0) (normalizedDedekindZeta K))

/- English proof (translation)
The claim follows from `Function.update_of_ne hs _ _`.
-/
theorem continuedDedekindZeta_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    continuedDedekindZeta K s = normalizedDedekindZeta K s :=
  Function.update_of_ne hs _ _

/- English proof (translation)
Rewrite using `[continuedDedekindZeta_of_ne_zero K (fun h ↦ by simp [h] at hs; linarith), normalizedDedekindZeta_eq K hs]`.
-/
theorem continuedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    continuedDedekindZeta K s = dedekindZeta K s := by
  rw [continuedDedekindZeta_of_ne_zero K (fun h ↦ by simp [h] at hs; linarith),
    normalizedDedekindZeta_eq K hs]

/- English proof (translation)
Establish `hnhds : ({1}ᶜ : Set ℂ) ∈ 𝓝 0` using `isOpen_compl_singleton.mem_nhds zero_ne_one`. Use `(Complex.differentiableOn_compl_singleton_and_continuousAt_iff hnhds).1 ⟨?_, ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ continuedDedekindZeta_of_ne_zero K hz.2` and prove the remaining obligations. Simplify using `only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff] at hz`. Conclude with `(((differentiable_discr_cpow_mul_gamma_inv K) z).mul (differentiableAt_completedDedekindZeta K hz.2 hz.1)).differentiableWithinAt`.

Take `⟨L, hL⟩` from `exists_tendsto_normalizedDedekindZeta_zero K`. Rewrite using `[continuedDedekindZeta, continuousAt_update_same, hL.limUnder_eq]`. Conclude with `hL`.
-/
theorem differentiableOn_continuedDedekindZeta :
    DifferentiableOn ℂ (continuedDedekindZeta K) {1}ᶜ := by
  have hnhds : ({1}ᶜ : Set ℂ) ∈ 𝓝 0 := isOpen_compl_singleton.mem_nhds zero_ne_one
  refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hnhds).1 ⟨?_, ?_⟩
  · refine DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ continuedDedekindZeta_of_ne_zero K hz.2
    simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff] at hz
    exact (((differentiable_discr_cpow_mul_gamma_inv K) z).mul
      (differentiableAt_completedDedekindZeta K hz.2 hz.1)).differentiableWithinAt
  · obtain ⟨L, hL⟩ := exists_tendsto_normalizedDedekindZeta_zero K
    rw [continuedDedekindZeta, continuousAt_update_same, hL.limUnder_eq]
    exact hL

/- English proof (translation)
The claim follows from `(differentiableOn_continuedDedekindZeta K).differentiableAt (isOpen_compl_singleton.mem_nhds hs)`.
-/
theorem differentiableAt_continuedDedekindZeta {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (continuedDedekindZeta K) s :=
  (differentiableOn_continuedDedekindZeta K).differentiableAt (isOpen_compl_singleton.mem_nhds hs)

/- English proof (translation)
Establish `h` using `residue_normalizedDedekindZeta_at_one K`. Establish `hres` using `tendsto_nhds_unique (h.comp tendsto_ofReal_nhdsGT_one) ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' (by filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)`. Rewrite using `[Function.comp_apply, normalizedDedekindZeta_eq K (by simpa using hs)]))`. Rewrite `h` using `[hres]`. Use `h.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds (one_ne_zero (α := ℂ)))] with s hs`. Rewrite using `[continuedDedekindZeta_of_ne_zero K hs]`.
-/
theorem tendsto_sub_one_mul_continuedDedekindZeta :
    Tendsto (fun s ↦ (s - 1) * continuedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have h := residue_normalizedDedekindZeta_at_one K
  have hres := tendsto_nhds_unique (h.comp tendsto_ofReal_nhdsGT_one)
    ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      rw [Function.comp_apply, normalizedDedekindZeta_eq K (by simpa using hs)]))
  rw [hres] at h
  refine h.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (isOpen_compl_singleton.mem_nhds (one_ne_zero (α := ℂ)))] with s hs
  rw [continuedDedekindZeta_of_ne_zero K hs]

/- English proof (translation)
Rewrite using `[← differentiableOn_univ]`. Use `(Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) univ_mem).1 ⟨?_, ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ Function.update_of_ne hz.2 _ _` and prove the remaining obligations. Conclude with `((differentiableAt_id.sub_const 1).mul (differentiableAt_continuedDedekindZeta K hz.2)).differentiableWithinAt`. Rewrite using `[continuousAt_update_same]`.

Conclude with `tendsto_sub_one_mul_continuedDedekindZeta K`.
-/
theorem differentiable_sub_one_mul_continuedDedekindZeta :
    Differentiable ℂ (Function.update (fun s ↦ (s - 1) * continuedDedekindZeta K s) 1
      (dedekindZeta_residue K : ℂ)) := by
  rw [← differentiableOn_univ]
  refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) univ_mem).1 ⟨?_, ?_⟩
  · refine DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ Function.update_of_ne hz.2 _ _
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_continuedDedekindZeta K hz.2)).differentiableWithinAt
  · rw [continuousAt_update_same]
    exact tendsto_sub_one_mul_continuedDedekindZeta K

/- English proof (translation)
Introduce `z _`. Distinguish the cases in `hz : z = 1`. Substitute `hz` using the available equality. Use `⟨2, (((differentiable_id.sub_const 1).mul (differentiable_sub_one_mul_continuedDedekindZeta K)).analyticAt 1).congr ?_⟩` and prove the remaining obligations. Use `filter_upwards [] with s`.

Distinguish the cases in `hs : s = 1`. Substitute `hs` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Pi.mul_apply, Function.update_of_ne hs, smul_eq_mul]`. Simplify using `only [id]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `((differentiableOn_continuedDedekindZeta K).analyticAt (isOpen_compl_singleton.mem_nhds hz)).meromorphicAt`.
-/
theorem meromorphicOn_continuedDedekindZeta : MeromorphicOn (continuedDedekindZeta K) univ := by
  intro z _
  by_cases hz : z = 1
  · subst hz
    refine ⟨2, (((differentiable_id.sub_const 1).mul
      (differentiable_sub_one_mul_continuedDedekindZeta K)).analyticAt 1).congr ?_⟩
    filter_upwards [] with s
    by_cases hs : s = 1
    · subst hs
      simp
    · rw [Pi.mul_apply, Function.update_of_ne hs, smul_eq_mul]
      simp only [id]
      ring
  · exact ((differentiableOn_continuedDedekindZeta K).analyticAt
      (isOpen_compl_singleton.mem_nhds hz)).meromorphicAt

end

end GroundTheory.Global
