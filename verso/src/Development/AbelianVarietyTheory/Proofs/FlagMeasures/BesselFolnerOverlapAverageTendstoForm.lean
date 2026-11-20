import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOneStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLimit

/- English proof (translation)
Establish `h1 : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h2 : g'ᴴ * Hpk k r * g' = Hpk k r` using `hg'`. Use `show (g * g')ᴴ * Hpk k r * (g * g') = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [h1, h2]`.
-/
theorem mul_mem_GG {k r : ℕ} {g g' : Mat k r} (hg : g ∈ GG k r) (hg' : g' ∈ GG k r) : g * g' ∈ GG k r := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : g'ᴴ * Hpk k r * g' = Hpk k r := hg'
  show (g * g')ᴴ * Hpk k r * (g * g') = Hpk k r
  calc (g * g')ᴴ * Hpk k r * (g * g') = g'ᴴ * (gᴴ * Hpk k r * g) * g' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

/- English proof (translation)
Introduce `g hg v hv`. Establish `hv' : v ∈ DD σ w` using `hv`. Use `show σ g v ∈ DD σ w`. Unfold `DD at hv'`. Proceed by induction on `hv' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g', hg', rfl⟩` from `hx`. Use `hσ.1.2 g hg g' hg'` as an intermediate fact. Establish `h2 : σ g (σ g' w) = σ (g * g') w` using `by rw [this]; rfl`. Rewrite using `[h2]`.

Conclude with `mem_DD σ w (mul_mem_GG hg hg')`. Consider the case `zero => simp`. Consider the case `add x y hx hy ihx ihy => rw [map_add]`. Conclude with `(DD σ w).add_mem (ihx hx) (ihy hy)`. Consider the case `smul c x hx ih => rw [map_smul]`.

Conclude with `(DD σ w).smul_mem c (ih hx)`.
-/
theorem DD_stable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  have hv' : v ∈ DD σ w := hv
  show σ g v ∈ DD σ w
  unfold DD at hv'
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', hg', rfl⟩ := hx
    have := hσ.1.2 g hg g' hg'
    have h2 : σ g (σ g' w) = σ (g * g') w := by rw [this]; rfl
    rw [h2]
    exact mem_DD σ w (mul_mem_GG hg hg')
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact (DD σ w).add_mem (ihx hx) (ihy hy)
  | smul c x hx ih => rw [map_smul]; exact (DD σ w).smul_mem c (ih hx)

/- English proof (translation)
Establish `hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2` using `Continuous.matrix_mul (A := fun q : Mt k r × Mt k r => (Matrix.of q.1 : Mat k r)) (B := fun q : Mt k r × Mt k r => (Matrix.of q.2 : Mat k r)) continuous_fst continuous_snd`. Establish `hm : MeasurableSet {q : Mt k r × Mt k r | q.2 ∈ Ω ∧ lmulM (Matrix.of q.1) q.2 ∈ Ω}` using `(measurable_snd hΩ).inter (hc.measurable hΩ)`. Conclude with `measurable_measure_prodMk_left hm`.
-/
theorem measurable_overlap {k r : ℕ} (μ : Measure (Mt k r)) [SFinite μ] {Ω : Set (Mt k r)}
    (hΩ : MeasurableSet Ω) :
    Measurable fun p : Mt k r => μ {s | s ∈ Ω ∧ lmulM (Matrix.of p) s ∈ Ω} := by
  have hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2 :=
    Continuous.matrix_mul (A := fun q : Mt k r × Mt k r => (Matrix.of q.1 : Mat k r))
      (B := fun q : Mt k r × Mt k r => (Matrix.of q.2 : Mat k r)) continuous_fst continuous_snd
  have hm : MeasurableSet {q : Mt k r × Mt k r | q.2 ∈ Ω ∧ lmulM (Matrix.of q.1) q.2 ∈ Ω} :=
    (measurable_snd hΩ).inter (hc.measurable hΩ)
  exact measurable_measure_prodMk_left hm

/- English proof (translation)
Use `haveI : SigmaFinite μ := hμ.1`. Establish `hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S` using `hμ.2.2.1`. Establish `heq : ∀ j, (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ) / ((μ (Om j)).toReal : ℂ) = ∫ p, (((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j)).toReal : ℝ) : ℂ) * f p ∂μ`. Introduce `j`. Rewrite using `[← integral_div]`.

Use `congr 1`. Use function extensionality and compare the values at `p`. Rewrite using `[ENNReal.toReal_div]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [heq]`. Use `tendsto_integral_of_dominated_convergence (fun p => ‖f p‖) (fun j => ?_) hf.norm (fun j => ?_) ?_` and prove the remaining obligations. Use `AEStronglyMeasurable.mul ?_ hf.1` and prove the remaining obligations. Use `((measurable_overlap μ (hO.1 j).1).div_const (μ (Om j))).ennreal_toReal` as an intermediate fact. Conclude with `(Complex.measurable_ofReal.comp this).aestronglyMeasurable`.

Use `Filter.Eventually.of_forall fun p => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]`. Use `mul_le_of_le_one_left (norm_nonneg _) ?_` and prove the remaining obligations. Establish `h1 : μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j) ≤ 1` using `ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono fun s hs => hs.1)`. Simplify using `using ENNReal.toReal_mono ENNReal.one_ne_top h1`.

Use `filter_upwards [hae] with p hp`. Establish `h1` using `GlobalTheory.T.folner_single_translate_proportion_tendsto_one k r S μ Om hO _ hp`. Establish `h2` using `(ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1`. Establish `h3` using `(Complex.continuous_ofReal.tendsto _).comp h2`. Establish `h4` using `h3.mul_const (f p)`.

Simplify `h4` using `[Function.comp_def]`.
-/
theorem tendsto_of_integrable {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {Om : ℕ → Set (Mt k r)} (hO : IsFolner S μ Om) {f : Mt k r → ℂ} (hf : Integrable f μ) :
    Filter.Tendsto (fun j => (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ)) Filter.atTop (nhds (∫ p, f p ∂μ)) := by
  haveI : SigmaFinite μ := hμ.1
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have heq : ∀ j, (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ) =
      ∫ p, (((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j)).toReal : ℝ) : ℂ) * f p ∂μ := by
    intro j
    rw [← integral_div]
    congr 1
    funext p
    rw [ENNReal.toReal_div]
    push_cast
    ring
  simp only [heq]
  refine tendsto_integral_of_dominated_convergence (fun p => ‖f p‖) (fun j => ?_) hf.norm (fun j => ?_) ?_
  · refine AEStronglyMeasurable.mul ?_ hf.1
    have := ((measurable_overlap μ (hO.1 j).1).div_const (μ (Om j))).ennreal_toReal
    exact (Complex.measurable_ofReal.comp this).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have h1 : μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j) ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono fun s hs => hs.1)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  · filter_upwards [hae] with p hp
    have h1 := GlobalTheory.T.folner_single_translate_proportion_tendsto_one k r S μ Om hO _ hp
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
    have h4 := h3.mul_const (f p)
    simpa [Function.comp_def] using h4

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide Om hO y hy ξ`. Establish `hint` using `(GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) (DD_stable hStd.2.1 w) hStd.2.2.2.2.2.2.2.1 y hy y hy).1`. Set `L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ` to `(innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)`. Establish `hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪ξ, T ξ⟫_ℂ` using `fun T => rfl`. Establish `hfun : (fun p : Mt k r => L (coef σ y y (Matrix.of p) • PiS (psiGen k r z c) π (Matrix.of p)⁻¹)) = fun p => coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ`.

Use function extensionality and compare the values at `p`. Rewrite using `[map_smul, hL, smul_eq_mul]`. Establish `hf` using `L.integrable_comp hint`. Establish `hI` using `L.integral_comp_comm hint`. Rewrite `hf`, `hI` using `[hfun]`.

Use `tendsto_of_integrable hSide.2.2.2.1 hO hf` as an intermediate fact. Rewrite `this` using `[hI]`. Conclude with `this`.
-/
theorem folner_limit : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide Om hO y hy ξ
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w)
    (DD_stable hStd.2.1 w) hStd.2.2.2.2.2.2.2.1 y hy y hy).1
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪ξ, T ξ⟫_ℂ := fun T => rfl
  have hfun : (fun p : Mt k r => L (coef σ y y (Matrix.of p) • PiS (psiGen k r z c) π (Matrix.of p)⁻¹)) =
      fun p => coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ := by
    funext p
    rw [map_smul, hL, smul_eq_mul]
  have hf := L.integrable_comp hint
  have hI := L.integral_comp_comm hint
  rw [hfun] at hf hI
  have := tendsto_of_integrable hSide.2.2.2.1 hO hf
  rw [hI] at this
  exact this

end GlobalTheory.SgInf.FolnerLimit
