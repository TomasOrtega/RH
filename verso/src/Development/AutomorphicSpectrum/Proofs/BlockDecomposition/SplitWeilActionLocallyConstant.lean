import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitSmoothnessHypothesis
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SplitContG

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 c₁ h₁ Φ hΦ g₀`. Establish `hH` using `GlobalTheory.CompanionTheory.SplitSmooth.stab_near hχ hχ1 h₁.1 hΦ`. Establish `hU : (fun g => g₀⁻¹ * g) ⁻¹' {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds g₀`. Establish `hc : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀` using `(continuous_const.mul continuous_id).continuousAt`. Establish `h1 : {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds (g₀⁻¹ * g₀)`.

Rewrite using `[inv_mul_cancel]`. Conclude with `hH`. Conclude with `hc h1`. Use `⟨_, hU, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hg' : GL2LocalData.piS χ c₁ (g₀⁻¹ * g) Φ = Φ` using `hg`.

Establish `e : g = g₀ * (g₀⁻¹ * g)` using `by group`. Rewrite using `[e, GlobalTheory.CompanionTheory.SplitPi.piS_mul hχ hχ1 c₁ hΦ, hg']`.
-/
theorem piS_locConst : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ c₁ : Fˣ →* ℂˣ, IsUnit1 c₁ → ∀ Φ ∈ GL2LocalData.SBE (F × F), ∀ g₀ : GL (Fin 2) F,
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piS χ c₁ g Φ = GL2LocalData.piS χ c₁ g₀ Φ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 c₁ h₁ Φ hΦ g₀
  have hH := GlobalTheory.CompanionTheory.SplitSmooth.stab_near hχ hχ1 h₁.1 hΦ
  have hU : (fun g => g₀⁻¹ * g) ⁻¹' {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds g₀ := by
    have hc : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀ := (continuous_const.mul continuous_id).continuousAt
    have h1 : {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds (g₀⁻¹ * g₀) := by
      rw [inv_mul_cancel]
      exact hH
    exact hc h1
  refine ⟨_, hU, fun g hg => ?_⟩
  have hg' : GL2LocalData.piS χ c₁ (g₀⁻¹ * g) Φ = Φ := hg
  have e : g = g₀ * (g₀⁻¹ * g) := by group
  rw [e, GlobalTheory.CompanionTheory.SplitPi.piS_mul hχ hχ1 c₁ hΦ, hg']

end GlobalTheory.CompanionTheory.SplitContG
