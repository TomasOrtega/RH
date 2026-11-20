import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobalSingular
import GroundTheory.AutomorphicForms.GL2.GJGlobalPoisson
import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeCont
import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeSummable

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

section Continuity

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

/- English proof (translation)
Set `T : {r : ℝ // 0 < r} → normOneGL K n → normOneGL K n → ℂ` to `fun t x y => conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))`. Establish `c1 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n => ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n)` using `by fun_prop`. Establish `c2 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n => ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n)` using `by fun_prop`. Establish `c4 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n => (p.1, ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n)⁻¹, ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n))` using `by fun_prop`. Establish `c3 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n => ∑' γ : GL (Fin n) K, Ξ (centralSection K n p.1 * ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n))`.

Establish `h5` using `hcont.comp c4`. Simplify `h5` using `only [Function.comp_def]`. Establish `hTc : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n => T p.1 p.2.1 p.2.2` using `((Complex.continuous_conj.comp (hφ₂.comp c1)).mul (hφ₁.comp c2)).mul c3`. Establish `hTb : ∀ t x y, ‖T t x y‖ ≤ B t`. Introduce `t x y`.

Simplify using `only [T, norm_mul, Complex.norm_conj]`. Conclude with `hB t x y`. Establish `hF : μ (fundamentalDomain Γ₁) < ⊤` using `measure_fundamentalDomain_rationalGLOne_lt_top μ`. Establish `: IsFiniteMeasure (μ.restrict (fundamentalDomain Γ₁))` using `⟨by rw [Measure.restrict_apply_univ]; exact hF⟩`. Establish `hloc : ∀ t₀ : {r : ℝ // 0 < r}, ∀ᶠ t in nhds t₀, B t ≤ B t₀ + 1` using `fun t₀ => (hBc.continuousAt.eventually (gt_mem_nhds (lt_add_one (B t₀)))).mono fun _ h => h.le`.

Establish `hinner : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n => ∫ y in fundamentalDomain Γ₁, T p.1 p.2 y ∂μ`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `p₀`. Use `continuousAt_of_dominated (bound := fun _ => B p₀.1 + 1) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun p => (hTc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable`.

Use `(hloc p₀.1).filter_mono (continuous_fst.continuousAt (x := p₀)).tendsto filter_upwards [this] with p hp` as an intermediate fact. Conclude with `Filter.Eventually.of_forall fun y => (hTb p.1 p.2 y).trans hp`. Conclude with `integrable_const _`. Conclude with `Filter.Eventually.of_forall fun y => (hTc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).continuousAt`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `t₀`. Unfold `thetaPairing`. Use `continuousAt_of_dominated (bound := fun _ => (B t₀ + 1) * (μ (fundamentalDomain Γ₁)).toReal) ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun t => (hinner.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable`. Use `filter_upwards [hloc t₀] with t ht`.

Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `integrable_const _`. Conclude with `Filter.Eventually.of_forall fun x => (hinner.comp (continuous_id.prodMk continuous_const)).continuousAt`.
-/
theorem continuous_thetaPairing {φ₁ φ₂ Ξ : AdelicGLn.AdelicGL K n → ℂ} (hφ₁ : Continuous φ₁)
    (hφ₂ : Continuous φ₂)
    (hcont : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ * p.2.2))
    {B : {r : ℝ // 0 < r} → ℝ} (hBc : Continuous B)
    (hB : ∀ t : {r : ℝ // 0 < r}, ∀ x y : normOneGL K n,
      ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ *
        ‖∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))‖ ≤ B t) :
    Continuous (thetaPairing μ φ₁ φ₂ Ξ) := by
  let T : {r : ℝ // 0 < r} → normOneGL K n → normOneGL K n → ℂ := fun t x y =>
    conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
        AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n))
  have c1 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n) := by fun_prop
  have c2 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n) := by fun_prop
  have c4 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      (p.1, ((p.2.1 : normOneGL K n) : AdelicGLn.AdelicGL K n)⁻¹,
        ((p.2.2 : normOneGL K n) : AdelicGLn.AdelicGL K n)) := by fun_prop
  have c3 : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      ∑' γ : GL (Fin n) K, Ξ (centralSection K n p.1 * ((p.2.1 : normOneGL K n) :
        AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * ((p.2.2 : normOneGL K n) :
          AdelicGLn.AdelicGL K n)) := by
    have h5 := hcont.comp c4
    simpa only [Function.comp_def] using h5
  have hTc : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n × normOneGL K n =>
      T p.1 p.2.1 p.2.2 :=
    ((Complex.continuous_conj.comp (hφ₂.comp c1)).mul (hφ₁.comp c2)).mul c3
  have hTb : ∀ t x y, ‖T t x y‖ ≤ B t := by
    intro t x y
    simp only [T, norm_mul, Complex.norm_conj]
    exact hB t x y
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict (fundamentalDomain Γ₁)) := ⟨by rw [Measure.restrict_apply_univ]; exact hF⟩

  have hloc : ∀ t₀ : {r : ℝ // 0 < r}, ∀ᶠ t in nhds t₀, B t ≤ B t₀ + 1 := fun t₀ =>
    (hBc.continuousAt.eventually (gt_mem_nhds (lt_add_one (B t₀)))).mono fun _ h => h.le

  have hinner : Continuous fun p : {r : ℝ // 0 < r} × normOneGL K n =>
      ∫ y in fundamentalDomain Γ₁, T p.1 p.2 y ∂μ := by
    rw [continuous_iff_continuousAt]
    intro p₀
    refine continuousAt_of_dominated (bound := fun _ => B p₀.1 + 1) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun p =>
        (hTc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const
          continuous_id))).aestronglyMeasurable
    · have := (hloc p₀.1).filter_mono (continuous_fst.continuousAt (x := p₀)).tendsto
      filter_upwards [this] with p hp
      exact Filter.Eventually.of_forall fun y => (hTb p.1 p.2 y).trans hp
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun y =>
        (hTc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).continuousAt
  rw [continuous_iff_continuousAt]
  intro t₀
  unfold thetaPairing
  refine continuousAt_of_dominated (bound := fun _ => (B t₀ + 1) * (μ (fundamentalDomain Γ₁)).toReal) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun t =>
      (hinner.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · filter_upwards [hloc t₀] with t ht
    refine Filter.Eventually.of_forall fun x => ?_
    calc ‖∫ y in fundamentalDomain Γ₁, T t x y ∂μ‖ ≤ (B t₀ + 1) * (μ.restrict (fundamentalDomain Γ₁) univ).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y =>
            (hTb t x y).trans ht)
      _ = (B t₀ + 1) * (μ (fundamentalDomain Γ₁)).toReal := by rw [Measure.restrict_apply_univ]
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun x =>
      (hinner.comp (continuous_id.prodMk continuous_const)).continuousAt

end Continuity

section Symmetry

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

local notation "Γ₁" => rationalGLOne K n

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, coe_diagonal]`.
-/
theorem coe_mul_diagonal_mul (t : {r : ℝ // 0 < r}) (a b : AdelicGLn.AdelicGL K n)
    (γ : GL (Fin n) K) :
    ((centralSection K n t * a * AdelicGLn.diagonal K n γ * b : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((centralSection K n t * a : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  rw [Units.val_mul, Units.val_mul, coe_diagonal]

/- English proof (translation)
Rewrite using `[← (Equiv.inv (GL (Fin n) K)).tsum_eq]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Equiv.inv_apply]`. Establish `e : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * y)⁻¹ = centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ * x`.

Rewrite using `[map_inv (AdelicGLn.diagonal K n)]`. Establish `e1 : (centralSection K n t * x⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * y)⁻¹ = (y⁻¹ * AdelicGLn.diagonal K n γ * x) * (centralSection K n t)⁻¹` using `by group`. Rewrite using `[e1, ← map_inv, ← centralSection_mul_comm t⁻¹ (y⁻¹ * AdelicGLn.diagonal K n γ * x)]`. Simplify using `only [mul_assoc]`. Rewrite using `[e, Units.val_mul, Units.val_mul, coe_diagonal]`.
-/
theorem tsum_inv_eq (Ψ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (t : {r : ℝ // 0 < r})
    (x y : AdelicGLn.AdelicGL K n) :
    ∑' γ : GL (Fin n) K, Ψ (((centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ * y)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
    ∑' γ : GL (Fin n) K, Ψ (((centralSection K n t⁻¹ * y⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
        (x : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [← (Equiv.inv (GL (Fin n) K)).tsum_eq]
  refine tsum_congr fun γ => ?_
  congr 1
  simp only [Equiv.inv_apply]
  have e : (centralSection K n t * x⁻¹ * AdelicGLn.diagonal K n γ⁻¹ * y)⁻¹ =
      centralSection K n t⁻¹ * y⁻¹ * AdelicGLn.diagonal K n γ * x := by
    rw [map_inv (AdelicGLn.diagonal K n)]
    have e1 : (centralSection K n t * x⁻¹ * (AdelicGLn.diagonal K n γ)⁻¹ * y)⁻¹ =
        (y⁻¹ * AdelicGLn.diagonal K n γ * x) * (centralSection K n t)⁻¹ := by group
    rw [e1, ← map_inv, ← centralSection_mul_comm t⁻¹ (y⁻¹ * AdelicGLn.diagonal K n γ * x)]
    simp only [mul_assoc]
  rw [e, Units.val_mul, Units.val_mul, coe_diagonal]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hn0 : 0 < n` using `by omega`. Use `set Φh := adelicMatrixFourier K Φ with hΦhdef`. Establish `hΦh : Φh ∈ matrixSchwartzBruhat K n` using `adelicMatrixFourier_mem hΦ`. Establish `hΦc : Continuous Φ` using `continuous_of_mem_matrixSchwartzBruhat hΦ`. Establish `hΦhc : Continuous Φh` using `continuous_of_mem_matrixSchwartzBruhat hΦh`.

Establish `h₁c : Continuous φ₁` using `h₁.1.continuous`. Establish `h₂c : Continuous φ₂` using `h₂.1.continuous`. Establish `h₂c' : Continuous fun g => conj (φ₂ g)` using `Complex.continuous_conj.comp h₂c`. Take `⟨B₁, hB₁⟩` from `CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₁`. Take `⟨B₂, hB₂⟩` from `CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂`.

Establish `hB₂' : ∃ C, ∀ g ∈ normOneGL K n, ‖conj (φ₂ g)‖ ≤ C` using `⟨B₂, fun g hg => by rw [Complex.norm_conj]; exact hB₂ g hg⟩`. Use `set F := fundamentalDomain Γ₁`. Establish `hF : μ F < ⊤` using `measure_fundamentalDomain_rationalGLOne_lt_top μ`. Establish `: IsFiniteMeasure (μ.restrict F)` using `⟨by rw [Measure.restrict_apply_univ]; exact hF⟩`. Use `set S : normOneGL K n → normOneGL K n → ℂ := fun x y => ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) …`.

Use `set Sh : normOneGL K n → normOneGL K n → ℂ := fun x y => ∑' ξ : Matrix (Fin n) (Fin n) K, Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K …`. Use `set ShG : normOneGL K n → normOneGL K n → ℂ := fun x y => ∑' γ : GL (Fin n) K, Φh (((centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) * ((x : AdelicGLn.AdelicGL K n) : Matrix ( …`. Establish `hP : ∀ x y : normOneGL K n, S x y = ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y`. Introduce `x y`. Use `(twisted_poisson_centralSection hn0 hΦ t x.2 y.2).2.2` as an intermediate fact.

Rewrite using `[hS, hSh]`. Simplify using `only`. Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression.

Take `⟨C₁, M₁, -, hC₁⟩` from `exists_bound_tsum hΦ h₁ h₂`. Take `⟨C₂, M₂, -, hC₂⟩` from `exists_bound_tsum hΦh h₂ h₁`. Establish `hA : ∀ x : normOneGL K n, ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) : Matr …`. Introduce `x`. Take `⟨C, hC⟩` from `exists_bound_tsum_one hΦ h₁ (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹)`.

Establish `key` using `setIntegral_mul_tsum_eq_tsum_GL μ hn h₁c h₁.1.isLeftInvariant h₁.2 ⟨B₁, hB₁⟩ hΦc (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹) (fun g => summable_norm_ratMat hΦ t _ g) ⟨C, fun g hg => (hC g hg).2⟩`. Establish `e : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ * AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) : Matrix (Fin n) …`. Introduce `y`. Rewrite using `[mul_assoc]`. Use `congr 2`.

Establish `e' : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) = conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * (φ₁ (y : AdelicGLn.AdelicGL K n) * S x y)`. Introduce `y`. Rewrite using `[hP x y, mul_assoc]`. Rewrite using `[setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e y, setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e' y, integral_const_mul, integral_const_mul, ← key]`. Establish `hB : ∀ y : normOneGL K n, ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y ∂μ = ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y ∂μ`.

Introduce `y`. Take `⟨C, hC⟩` from `exists_bound_tsum_one hΦh h₂ (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹)`. Establish `key` using `setIntegral_mul_tsum_eq_tsum_GL μ hn h₂c' (isLeftInvariant_conj h₂.1.isLeftInvariant) (isCuspidal_conj h₂.2) hB₂' hΦhc (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹) (fun g => summable_norm_ratMat hΦh t⁻¹ _ g) ⟨C, fun g hg => by rw [Complex.norm_conj]; exact (hC g hg). …`. Establish `e1 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y = φ₁ (y : AdelicGLn.AdelicGL K n) * (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * Sh x y)` using `fun x => by ring`. Establish `e2 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y = φ₁ (y : AdelicGLn.AdelicGL K n) * (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * ShG x y)` using `fun x => by ring`.

Rewrite using `[setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e1 x, setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e2 x, integral_const_mul, integral_const_mul]`. Use `congr 1`. Establish `hmeasSh : Continuous fun p : normOneGL K n × normOneGL K n => Sh p.1 p.2`. Establish `hc` using `continuous_tsum_ratMat hΦh`. Establish `h4 : Continuous fun p : normOneGL K n × normOneGL K n => (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n)))` using `by fun_prop`.

Establish `h5` using `hc.comp h4`. Simplify `h5` using `only [Function.comp_def]`. Establish `hmeasShG : Continuous fun p : normOneGL K n × normOneGL K n => ShG p.1 p.2`. Establish `hc` using `continuous_tsum_GL hΦh`. Establish `h4 : Continuous fun p : normOneGL K n × normOneGL K n => (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n)))` using `by fun_prop`.

Establish `h5` using `hc.comp h4`. Simplify using `only [Function.comp_def] at h5`. Use `h5.congr fun p => tsum_congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[coe_mul_diagonal_mul]`. Establish `hbdSh : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂`.

Introduce `x y`. Take `⟨hs, hb⟩` from `hC₂ y y.2 x x.2 t⁻¹`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm ‖φ₂ _‖]`.

Conclude with `mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) (mul_nonneg (norm_nonneg _) (norm_nonneg _))`. Use `_ ≤ _ := hb`. Establish `hbdShG : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂`. Introduce `x y`. Take `⟨hs, hb⟩` from `hC₂ y y.2 x x.2 t⁻¹`.

Rewrite using `[norm_mul, norm_mul, Complex.norm_conj]`. Establish `hs'` using `hs.comp_injective (Units.val_injective (α := Matrix (Fin n) (Fin n) K))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm ‖φ₂ _‖]`. Use `mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hs').trans ?_) (mul_nonneg (norm_nonneg _) (norm_nonneg _))` and prove the remaining obligations.

Conclude with `Summable.tsum_le_tsum_of_inj _ Units.val_injective (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hs' hs`. Use `_ ≤ _ := hb`. Establish `hint : ∀ T : normOneGL K n → normOneGL K n → ℂ, Continuous (fun p : normOneGL K n × normOneGL K n => T p.1 p.2) → (∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * T x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂) → Int …`. Introduce `T hT hTb`. Use `Integrable.of_bound ?_ (C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂) (Eventually.of_forall fun p => hTb p.1 p.2)` and prove the remaining obligations.

Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Conclude with `((h₂c'.comp (continuous_subtype_val.comp continuous_fst)).mul (h₁c.comp (continuous_subtype_val.comp continuous_snd))).mul hT`. Unfold `thetaPairing`. Simplify using `only`. Rewrite using `[setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => hA x]`.

Establish `e3 : ∀ x y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) = ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y)` using `fun x y => by ring`. Repeatedly rewrite using `[e3, integral_const_mul]`. Use `congr 1`. Rewrite using `[integral_integral_swap (hint Sh hmeasSh hbdSh)]`. Repeatedly rewrite using `[hB]`.

Rewrite using `[← integral_integral_swap (hint ShG hmeasShG hbdShG)]`. Use `setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => ?_` and prove the remaining obligations. Use `setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => ?_` and prove the remaining obligations. Rewrite using `[tsum_inv_eq]`.
-/
theorem thetaPairing_eq (hn : 2 ≤ n) {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ}
    (h₁ : φ₁ ∈ cuspForms K n) (h₂ : φ₂ ∈ cuspForms K n)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n)
    (t : {r : ℝ // 0 < r}) :
    thetaPairing μ φ₁ φ₂ (fun g => Φ (g : Matrix (Fin n) (Fin n) 𝔸[K])) t =
      ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * thetaPairing μ φ₁ φ₂
        (fun g => adelicMatrixFourier K Φ ((g⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K])) t := by
  have hn0 : 0 < n := by omega
  set Φh := adelicMatrixFourier K Φ with hΦhdef
  have hΦh : Φh ∈ matrixSchwartzBruhat K n := adelicMatrixFourier_mem hΦ
  have hΦc : Continuous Φ := continuous_of_mem_matrixSchwartzBruhat hΦ
  have hΦhc : Continuous Φh := continuous_of_mem_matrixSchwartzBruhat hΦh
  have h₁c : Continuous φ₁ := h₁.1.continuous
  have h₂c : Continuous φ₂ := h₂.1.continuous
  have h₂c' : Continuous fun g => conj (φ₂ g) := Complex.continuous_conj.comp h₂c
  obtain ⟨B₁, hB₁⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₁
  obtain ⟨B₂, hB₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂
  have hB₂' : ∃ C, ∀ g ∈ normOneGL K n, ‖conj (φ₂ g)‖ ≤ C :=
    ⟨B₂, fun g hg => by rw [Complex.norm_conj]; exact hB₂ g hg⟩
  set F := fundamentalDomain Γ₁
  have hF : μ F < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict F) := ⟨by rw [Measure.restrict_apply_univ]; exact hF⟩

  set S : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hS
  set Sh : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' ξ : Matrix (Fin n) (Fin n) K, Φh (((centralSection K n t⁻¹ *
      (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat ξ * ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hSh
  set ShG : normOneGL K n → normOneGL K n → ℂ := fun x y =>
    ∑' γ : GL (Fin n) K, Φh (((centralSection K n t⁻¹ *
      (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) with hShG

  have hP : ∀ x y : normOneGL K n, S x y = ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y := by
    intro x y
    have := (twisted_poisson_centralSection hn0 hΦ t x.2 y.2).2.2
    rw [hS, hSh]
    simp only
    rw [this]
    push_cast
    rfl

  obtain ⟨C₁, M₁, -, hC₁⟩ := exists_bound_tsum hΦ h₁ h₂
  obtain ⟨C₂, M₂, -, hC₂⟩ := exists_bound_tsum hΦh h₂ h₁

  have hA : ∀ x : normOneGL K n,
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) ∂μ =
      ∫ y in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) ∂μ := by
    intro x
    obtain ⟨C, hC⟩ := exists_bound_tsum_one hΦ h₁
      (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹)
    have key := setIntegral_mul_tsum_eq_tsum_GL μ hn h₁c h₁.1.isLeftInvariant h₁.2
      ⟨B₁, hB₁⟩ hΦc (centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹)
      (fun g => summable_norm_ratMat hΦ t _ g) ⟨C, fun g hg => (hC g hg).2⟩
    have e : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) *
        ∑' γ : GL (Fin n) K, Φ ((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ *
          AdelicGLn.diagonal K n γ * (y : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n) :
            Matrix (Fin n) (Fin n) 𝔸[K]) =
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * (φ₁ (y : AdelicGLn.AdelicGL K n) *
          ∑' γ : GL (Fin n) K, Φ (((centralSection K n t * (x : AdelicGLn.AdelicGL K n)⁻¹ :
            AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
              ratMat (γ : Matrix (Fin n) (Fin n) K) *
                ((y : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) := by
      intro y
      rw [mul_assoc]
      congr 2
    have e' : ∀ y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) =
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * (φ₁ (y : AdelicGLn.AdelicGL K n) * S x y) := by
      intro y
      rw [hP x y, mul_assoc]
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e y,
      setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => e' y,
      integral_const_mul, integral_const_mul, ← key]

  have hB : ∀ y : normOneGL K n,
      ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        Sh x y ∂μ =
      ∫ x in F, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) *
        ShG x y ∂μ := by
    intro y
    obtain ⟨C, hC⟩ := exists_bound_tsum_one hΦh h₂
      (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹)
    have key := setIntegral_mul_tsum_eq_tsum_GL μ hn h₂c' (isLeftInvariant_conj h₂.1.isLeftInvariant)
      (isCuspidal_conj h₂.2) hB₂' hΦhc (centralSection K n t⁻¹ * (y : AdelicGLn.AdelicGL K n)⁻¹)
      (fun g => summable_norm_ratMat hΦh t⁻¹ _ g)
      ⟨C, fun g hg => by rw [Complex.norm_conj]; exact (hC g hg).2⟩
    have e1 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y = φ₁ (y : AdelicGLn.AdelicGL K n) *
          (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * Sh x y) := fun x => by ring
    have e2 : ∀ x : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y = φ₁ (y : AdelicGLn.AdelicGL K n) *
          (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * ShG x y) := fun x => by ring
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e1 x,
      setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => e2 x,
      integral_const_mul, integral_const_mul]
    congr 1

  have hmeasSh : Continuous fun p : normOneGL K n × normOneGL K n => Sh p.1 p.2 := by
    have hc := continuous_tsum_ratMat hΦh
    have h4 : Continuous fun p : normOneGL K n × normOneGL K n =>
        (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n))) := by fun_prop
    have h5 := hc.comp h4
    simpa only [Function.comp_def] using h5
  have hmeasShG : Continuous fun p : normOneGL K n × normOneGL K n => ShG p.1 p.2 := by
    have hc := continuous_tsum_GL hΦh
    have h4 : Continuous fun p : normOneGL K n × normOneGL K n =>
        (t⁻¹, ((p.2 : AdelicGLn.AdelicGL K n))⁻¹, ((p.1 : AdelicGLn.AdelicGL K n))) := by fun_prop
    have h5 := hc.comp h4
    simp only [Function.comp_def] at h5
    refine h5.congr fun p => tsum_congr fun γ => ?_
    rw [coe_mul_diagonal_mul]
  have hbdSh : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := by
    intro x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖Sh x y‖
        ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
          rw [mul_comm ‖φ₂ _‖]
          exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ _ := hb
  have hbdShG : ∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * ShG x y‖ ≤ C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂ := by
    intro x y
    obtain ⟨hs, hb⟩ := hC₂ y y.2 x x.2 t⁻¹
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hs' := hs.comp_injective (Units.val_injective (α := Matrix (Fin n) (Fin n) K))
    calc ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ * ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖ShG x y‖
        ≤ ‖φ₁ (y : AdelicGLn.AdelicGL K n)‖ * ‖φ₂ (x : AdelicGLn.AdelicGL K n)‖ *
          ∑' ξ : Matrix (Fin n) (Fin n) K, ‖Φh (((centralSection K n t⁻¹ *
            (y : AdelicGLn.AdelicGL K n)⁻¹ : AdelicGLn.AdelicGL K n) :
              Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
                ((x : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))‖ := by
          rw [mul_comm ‖φ₂ _‖]
          refine mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm hs').trans ?_)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          exact Summable.tsum_le_tsum_of_inj _ Units.val_injective (fun _ _ => norm_nonneg _)
            (fun _ => le_rfl) hs' hs
      _ ≤ _ := hb
  have hint : ∀ T : normOneGL K n → normOneGL K n → ℂ,
      Continuous (fun p : normOneGL K n × normOneGL K n => T p.1 p.2) →
      (∀ x y : normOneGL K n, ‖conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * T x y‖ ≤
        C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂) →
      Integrable (Function.uncurry fun x y : normOneGL K n =>
        conj (φ₂ (x : AdelicGLn.AdelicGL K n)) * φ₁ (y : AdelicGLn.AdelicGL K n) * T x y)
        ((μ.restrict F).prod (μ.restrict F)) := by
    intro T hT hTb
    refine Integrable.of_bound ?_ (C₂ * (max 1 ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)⁻¹) ^ M₂)
      (Eventually.of_forall fun p => hTb p.1 p.2)
    refine Continuous.aestronglyMeasurable ?_
    exact ((h₂c'.comp (continuous_subtype_val.comp continuous_fst)).mul
      (h₁c.comp (continuous_subtype_val.comp continuous_snd))).mul hT

  unfold thetaPairing
  dsimp only
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => hA x]
  have e3 : ∀ x y : normOneGL K n, conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
      φ₁ (y : AdelicGLn.AdelicGL K n) * (((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * Sh x y) =
      ((((t : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * (conj (φ₂ (x : AdelicGLn.AdelicGL K n)) *
        φ₁ (y : AdelicGLn.AdelicGL K n) * Sh x y) := fun x y => by ring
  simp_rw [e3, integral_const_mul]
  congr 1
  rw [integral_integral_swap (hint Sh hmeasSh hbdSh)]
  simp_rw [hB]
  rw [← integral_integral_swap (hint ShG hmeasShG hbdShG)]
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun x _ => ?_
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun y _ => ?_
  rw [tsum_inv_eq]

end Symmetry

end GJGlobal

end

end GroundTheory.Automorphic
