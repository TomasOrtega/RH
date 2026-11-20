import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Use `⟨fun s => Real.smoothTransition (s - R) * Real.smoothTransition (a + 1 - s), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))`. Introduce `s`. Conclude with `mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)`. Conclude with `mul_pos (Real.smoothTransition.pos_of_pos (by linarith)) (Real.smoothTransition.pos_of_pos (by linarith))`.

Introduce `s hs`. Simplify using `only [Real.smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith), zero_mul]`. Introduce `s hs`. Simplify using `only [Real.smoothTransition.zero_of_nonpos (show a + 1 - s ≤ 0 by linarith), mul_zero]`.
-/
lemma sr_window {R a : ℝ} (h : R < a) : ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ s, 0 ≤ β s) ∧ 0 < β a ∧
    (∀ s, s ≤ R → β s = 0) ∧ ∀ s, a + 1 ≤ s → β s = 0 := by
  refine ⟨fun s => Real.smoothTransition (s - R) * Real.smoothTransition (a + 1 - s), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  · intro s
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
      (Real.smoothTransition.pos_of_pos (by linarith))
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith), zero_mul]
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show a + 1 - s ≤ 0 by linarith), mul_zero]

/- English proof (translation)
Establish `e1 : cls μ f = hf.toLp _` using `dif_pos hf`. Establish `e2 : cls μ g = hg.toLp _` using `dif_pos hg`. Establish `hae : (fun y : G n => ⟪(hf.toLp _ : Lp V 2 μ) y, (hg.toLp _ : Lp V 2 μ) y⟫_ℂ) =ᵐ[μ] fun y : G n => ⟪f y.val, g y.val⟫_ℂ` using `by filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b`. Rewrite using `[a, b]`. Use `⟨(L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)).congr hae, ?_⟩` and prove the remaining obligations.

Rewrite using `[e1, e2, L2.inner_def]`. Conclude with `integral_congr_ae hae`.
-/
lemma sr_inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f g : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    Integrable (fun y : G n => ⟪f y.val, g y.val⟫_ℂ) μ ∧
      ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := dif_pos hf
  have e2 : cls μ g = hg.toLp _ := dif_pos hg
  have hae : (fun y : G n => ⟪(hf.toLp _ : Lp V 2 μ) y, (hg.toLp _ : Lp V 2 μ) y⟫_ℂ) =ᵐ[μ]
      fun y : G n => ⟪f y.val, g y.val⟫_ℂ := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b
    rw [a, b]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)).congr hae, ?_⟩
  rw [e1, e2, L2.inner_def]
  exact integral_congr_ae hae

/- English proof (translation)
Use `show y.val.det ≠ 0`. Conclude with `(Matrix.isUnits_det_units y).ne_zero`.
-/
lemma sr_val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

/- English proof (translation)
Establish `hae : ψ =ᵐ[μ] 0` using `(integral_eq_zero_iff_of_nonneg h0 hi).1 hz`. Use `(Continuous.ae_eq_iff_eq μ hc continuous_zero).1 hae` as an intermediate fact. Introduce `y`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
lemma sr_eq_zero {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {ψ : G n → ℝ} (hc : Continuous ψ) (h0 : ∀ y, 0 ≤ ψ y) (hi : Integrable ψ μ) (hz : ∫ y, ψ y ∂μ = 0) :
    ∀ y, ψ y = 0 := by
  have hae : ψ =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg h0 hi).1 hz
  have := (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 hae
  intro y
  rw [this]
  rfl

/- English proof (translation)
Introduce `n _ _ μ _ E _ Ω T F c hStd g T₀ h hg hh H`. Take `⟨hLg, hUn, hRC, hSobG, hAlg, hWS, hWC, hCS, hSO, hPW, -, -, -, -, hOm, -⟩` from `hStd`. Establish `hCptSob : CptSob` using `hCS.2.2.2.2.2.2.1`. Take `⟨c₀, hc₀⟩` from `hWS n`. Use `⟨|c₀| * (1 + |T₀|), ?_⟩` and prove the remaining obligations.

Introduce `v f hRow y₀ hy₀ hR`. Take `⟨hfSob, hfSec, hfRow⟩` from `hRow`. Take `⟨β, hβs, hβ0, hβpos, hβlo, hβhi⟩` from `sr_window hR`. Take `⟨-, -, hLk, hLs, -, -, -⟩` from `hLg n`. Use `set φ : Mat n → E.V := fun y => ((β (lg y) : ℝ) : ℂ) • f y with hφ`.

Establish `hφs : ContDiffOn ℝ ∞ φ (GLs n)`. Establish `h1 : ContDiffOn ℝ ∞ (fun y : Mat n => ((β (lg y) : ℝ) : ℂ)) (GLs n)` using `Complex.ofRealCLM.contDiff.comp_contDiffOn (hβs.comp_contDiffOn hLs)`. Conclude with `h1.smul hfSob.1`. Establish `hφsec : IsSec E φ`. Introduce `y hy k`.

Establish `hl : lg (y * k.1) = lg y`. Use `hLk y hy 1 k` as an intermediate fact. Simplify using `using this`. Simplify using `only [hφ, hl, hfSec y hy k, map_smul]`. Establish `hφc : Cpt φ`.

Use `⟨lg y₀ + 1, fun y _ hy => ?_⟩` and prove the remaining obligations. Simplify using `only [hφ, hβhi _ hy.le, Complex.ofReal_zero, zero_smul]`. Establish `hφCE : φ ∈ CE E` using `⟨hφs, hφsec⟩`. Establish `hφSob : Sob μ φ` using `(hCptSob n μ E.V hLg hRC φ hφs hφc).1`. Take `⟨u, huW, hu0⟩` from `hWC n E φ hφCE hφc`.

Take `⟨C, hC⟩` from `hSO n μ E Ω T F hLg hUn hRC hSobG hAlg hCS hOm h hh`. Take `⟨f', hf'Sob, hf'Sec, hf'cls, -⟩` from `hC (cls μ φ) (subset_closure ⟨φ, hφSob, hφsec, rfl⟩)`. Establish `h1G : (1 : Mat n) ∈ GLs n` using `by show (1 : Mat n).det ≠ 0`. Simplify using the standard rewrite rules. Establish `hf'1 : f' 1 = 0`.

Rewrite using `[← H φ hφCE hφc u huW hu0 f' hf'Sob hf'Sec hf'cls 1 h1G]`. Establish `: ∀ t, (g t : ℂ) • u t 1 = 0`. Introduce `t`. Distinguish the cases in `hgt : g t = 0`. Simplify using `[hgt]`.

Establish `ht : |t| ≤ T₀`. Assume the negation of the conclusion as `hcon`. Conclude with `hgt (hg.2.2 t (not_le.1 hcon))`. Establish `hut : u t 1 = 0`. Use `hc₀ E u huW t 1 h1G fun y hy hly => ?_` and prove the remaining obligations.

Rewrite using `[one_mul, hu0 y hy]`. Establish `hb : lg y ≤ |c₀| * (1 + |T₀|)`. Use `hly.trans ?_` and prove the remaining obligations. Establish `h1 : c₀ ≤ |c₀|` using `le_abs_self _`. Establish `h2 : |t| ≤ |T₀|` using `ht.trans (le_abs_self _)`.

Establish `h3 : 0 ≤ |c₀|` using `abs_nonneg _`. Establish `h4 : 0 ≤ |t|` using `abs_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [hφ, hβlo _ hb, Complex.ofReal_zero, zero_smul]`. Simplify using `[hut]`.

Simplify using `[this]`. Establish `hzero : ⟪cls μ f, cls μ φ⟫_ℂ = 0`. Rewrite using `[hfRow φ f' hφSob hφsec hf'Sob hf'Sec hf'cls, hf'1, inner_zero_right]`. Establish `hfL : MemLp (fun y : G n => f y.val) 2 μ` using `hfSob.2 []`. Establish `hφL : MemLp (fun y : G n => φ y.val) 2 μ` using `hφSob.2 []`.

Take `⟨hI, hE⟩` from `sr_inner_cls μ hfL hφL`. Use `set ψ : G n → ℝ := fun y => β (lg y.val) * ‖f y.val‖ ^ 2 with hψ`. Establish `hpt : ∀ y : G n, ⟪f y.val, φ y.val⟫_ℂ = (ψ y : ℂ)`. Introduce `y`. Simplify using `only [hφ, hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hψi : Integrable ψ μ`. Use `hI.re` as an intermediate fact. Use `this.congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `[hpt y]`. Establish `hψz : ∫ y, ψ y ∂μ = 0`. Establish `h2 : ((∫ y, ψ y ∂μ : ℝ) : ℂ) = 0`. Rewrite using `[← integral_complex_ofReal, ← hzero, hE]`. Conclude with `integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)`.

Conclude with `h2` after adjusting the coercions. Establish `hlc : Continuous (fun y : G n => lg y.val)` using `hLs.continuousOn.comp_continuous Units.continuous_val sr_val_mem`. Establish `hfc : Continuous (fun y : G n => f y.val)` using `hfSob.1.continuousOn.comp_continuous Units.continuous_val sr_val_mem`. Establish `hψc : Continuous ψ` using `(hβs.continuous.comp hlc).mul (hfc.norm.pow 2)`. Establish `hψ0 : ∀ y, 0 ≤ ψ y` using `fun y => mul_nonneg (hβ0 _) (by positivity)`.

Establish `hall` using `sr_eq_zero μ hψc hψ0 hψi hψz`. Use `hall (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀)` as an intermediate fact. Establish `hval : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀ : G n).val = y₀` using `rfl`. Simplify using `only [hψ, hval] at this`. Break down `mul_eq_zero.1 this with h' | h'` into its components or cases.

Conclude with `absurd h' hβpos.ne'`. Simplify using `using h'`.
-/
theorem supportRow : SupportRow := by
  intro n _ _ μ _ E _ Ω T F c hStd g T₀ h hg hh H
  obtain ⟨hLg, hUn, hRC, hSobG, hAlg, hWS, hWC, hCS, hSO, hPW, -, -, -, -, hOm, -⟩ := hStd
  have hCptSob : CptSob := hCS.2.2.2.2.2.2.1
  obtain ⟨c₀, hc₀⟩ := hWS n
  refine ⟨|c₀| * (1 + |T₀|), ?_⟩
  intro v f hRow y₀ hy₀ hR
  obtain ⟨hfSob, hfSec, hfRow⟩ := hRow
  obtain ⟨β, hβs, hβ0, hβpos, hβlo, hβhi⟩ := sr_window hR
  obtain ⟨-, -, hLk, hLs, -, -, -⟩ := hLg n
  set φ : Mat n → E.V := fun y => ((β (lg y) : ℝ) : ℂ) • f y with hφ

  have hφs : ContDiffOn ℝ ∞ φ (GLs n) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => ((β (lg y) : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hβs.comp_contDiffOn hLs)
    exact h1.smul hfSob.1
  have hφsec : IsSec E φ := by
    intro y hy k
    have hl : lg (y * k.1) = lg y := by
      have := hLk y hy 1 k
      simpa using this
    simp only [hφ, hl, hfSec y hy k, map_smul]
  have hφc : Cpt φ := by
    refine ⟨lg y₀ + 1, fun y _ hy => ?_⟩
    simp only [hφ, hβhi _ hy.le, Complex.ofReal_zero, zero_smul]
  have hφCE : φ ∈ CE E := ⟨hφs, hφsec⟩
  have hφSob : Sob μ φ := (hCptSob n μ E.V hLg hRC φ hφs hφc).1
  obtain ⟨u, huW, hu0⟩ := hWC n E φ hφCE hφc
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSobG hAlg hCS hOm h hh
  obtain ⟨f', hf'Sob, hf'Sec, hf'cls, -⟩ := hC (cls μ φ) (subset_closure ⟨φ, hφSob, hφsec, rfl⟩)
  have h1G : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp

  have hf'1 : f' 1 = 0 := by
    rw [← H φ hφCE hφc u huW hu0 f' hf'Sob hf'Sec hf'cls 1 h1G]
    have : ∀ t, (g t : ℂ) • u t 1 = 0 := by
      intro t
      by_cases hgt : g t = 0
      · simp [hgt]
      · have ht : |t| ≤ T₀ := by
          by_contra hcon
          exact hgt (hg.2.2 t (not_le.1 hcon))
        have hut : u t 1 = 0 := by
          refine hc₀ E u huW t 1 h1G fun y hy hly => ?_
          rw [one_mul, hu0 y hy]
          have hb : lg y ≤ |c₀| * (1 + |T₀|) := by
            refine hly.trans ?_
            have h1 : c₀ ≤ |c₀| := le_abs_self _
            have h2 : |t| ≤ |T₀| := ht.trans (le_abs_self _)
            have h3 : 0 ≤ |c₀| := abs_nonneg _
            have h4 : 0 ≤ |t| := abs_nonneg _
            nlinarith
          simp only [hφ, hβlo _ hb, Complex.ofReal_zero, zero_smul]
        simp [hut]
    simp [this]
  have hzero : ⟪cls μ f, cls μ φ⟫_ℂ = 0 := by
    rw [hfRow φ f' hφSob hφsec hf'Sob hf'Sec hf'cls, hf'1, inner_zero_right]

  have hfL : MemLp (fun y : G n => f y.val) 2 μ := hfSob.2 []
  have hφL : MemLp (fun y : G n => φ y.val) 2 μ := hφSob.2 []
  obtain ⟨hI, hE⟩ := sr_inner_cls μ hfL hφL
  set ψ : G n → ℝ := fun y => β (lg y.val) * ‖f y.val‖ ^ 2 with hψ
  have hpt : ∀ y : G n, ⟪f y.val, φ y.val⟫_ℂ = (ψ y : ℂ) := by
    intro y
    simp only [hφ, hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hψi : Integrable ψ μ := by
    have := hI.re
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [hpt y]
  have hψz : ∫ y, ψ y ∂μ = 0 := by
    have h2 : ((∫ y, ψ y ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hzero, hE]
      exact integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    exact_mod_cast h2
  have hlc : Continuous (fun y : G n => lg y.val) :=
    hLs.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hfc : Continuous (fun y : G n => f y.val) :=
    hfSob.1.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hψc : Continuous ψ := (hβs.continuous.comp hlc).mul (hfc.norm.pow 2)
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (hβ0 _) (by positivity)
  have hall := sr_eq_zero μ hψc hψ0 hψi hψz
  have := hall (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀)
  have hval : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀ : G n).val = y₀ := rfl
  simp only [hψ, hval] at this
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hβpos.ne'
  · simpa using h'

end GlobalTheory.CompanionTheory.KerFc
