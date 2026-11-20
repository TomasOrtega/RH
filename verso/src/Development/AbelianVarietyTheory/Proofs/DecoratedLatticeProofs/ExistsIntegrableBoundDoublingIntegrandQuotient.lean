import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecrStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Dom

/- English proof (translation)
Introduce `D V μ m hm f₁ f₂ hf₁ hf₂ C' c hC' C N`. Establish `hC'1 : 1 ≤ C'`. Establish `h` using `hC' 1 1`. Establish `e : io V ((1 : GA D V), (1 : GA D V)) = 1` using `map_one (io V)`. Simplify using `only [e, GlobalTheory.Grow.height_one, mul_one, one_pow] at h`.

Conclude with `h`. Use `set K : ℝ := max C 0 * (C' * 4 ^ c) ^ N with hK`. Establish `i₁` using `GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ hf₁ (c * N)`. Establish `i₂` using `GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ hf₂ (c * N)`. Use `⟨fun q => K * ((GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * ‖f₁ q.1.out‖) * (GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N) * ‖f₂ q.2.out‖)), (i₁.mul_prod i₂).const_mul K, ?_⟩` and prove the remaining obligations.

Introduce `E hE hEb q`. Take `⟨γ₁, hγ₁, h₁⟩` from `GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out`. Take `⟨γ₂, hγ₂, h₂⟩` from `GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out`. Establish `hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out))`. Establish `e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out)`.

Rewrite using `[← map_mul]`. Both sides reduce to the same expression. Rewrite using `[e, hE _ (io_mem_GQ V hγ₁ hγ₂)]`. Establish `hq₁` using `GlobalTheory.Grow.one_le_quotHeight V q.1.out`. Establish `hq₂` using `GlobalTheory.Grow.one_le_quotHeight V q.2.out`.

Establish `hx₁` using `GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)`. Establish `hx₂` using `GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)`. Establish `hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N))`. Rewrite using `[hinv]`. Use `(hEb _).trans ?_` and prove the remaining obligations.

Establish `hh` using `hC' (γ₁ * q.1.out) (γ₂ * q.2.out)`. Establish `hprod : GlobalTheory.Grow.height V (γ₁ * q.1.out) * GlobalTheory.Grow.height V (γ₂ * q.2.out) ≤ 4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out)`. Use `mul_le_mul h₁ h₂ (by linarith) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤ C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c`.

Use `hh.trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← mul_pow]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hprod c) (by linarith)`. Establish `h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out))` using `GlobalTheory.Grow.one_le_height _ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hK, pow_mul, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hμ : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1`. Rewrite using `[norm_inv, Circle.norm_coe, inv_one]`. Simplify using `only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, norm_mul, hμ, mul_one, Complex.norm_conj]`.

Establish `hK0 : 0 ≤ K`. Rewrite using `[hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg (by linarith) (by positivity)) N)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_integrable_bound_dblIntegrandQ : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q := by
  intro D V μ m hm f₁ f₂ hf₁ hf₂ C' c hC' C N
  have hC'1 : 1 ≤ C' := by
    have h := hC' 1 1
    have e : io V ((1 : GA D V), (1 : GA D V)) = 1 := map_one (io V)
    simp only [e, GlobalTheory.Grow.height_one, mul_one, one_pow] at h
    exact h
  set K : ℝ := max C 0 * (C' * 4 ^ c) ^ N with hK
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ hf₁ (c * N)
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ hf₂ (c * N)
  refine ⟨fun q => K * ((GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * ‖f₁ q.1.out‖) *
      (GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N) * ‖f₂ q.2.out‖)), (i₁.mul_prod i₂).const_mul K, ?_⟩
  intro E hE hEb q
  obtain ⟨γ₁, hγ₁, h₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, h₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) *
      GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
    rw [hinv]
    refine (hEb _).trans ?_
    have hh := hC' (γ₁ * q.1.out) (γ₂ * q.2.out)
    have hprod : GlobalTheory.Grow.height V (γ₁ * q.1.out) * GlobalTheory.Grow.height V (γ₂ * q.2.out) ≤
        4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
      have := mul_le_mul h₁ h₂ (by linarith) (by linarith)
      linarith
    have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
        C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c := by
      refine hh.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hprod c) (by linarith)
    have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
    calc C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N
        ≤ max C 0 * (C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N) (le_max_right _ _)
      _ = K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
          rw [hK, pow_mul, pow_mul]; ring
  have hμ : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, norm_mul, hμ, mul_one, Complex.norm_conj]
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg (by linarith) (by positivity)) N)
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

end GlobalTheory.Core.Rk.Dom
