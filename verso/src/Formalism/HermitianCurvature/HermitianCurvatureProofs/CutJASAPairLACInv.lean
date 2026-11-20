import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnipotentEquivHolds

open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ D φ₀ _hφ p₀ hp₀ g`. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN` as an intermediate fact. Use `Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'` as an intermediate fact. Take `⟨h1, h2, h3, h4⟩` from `hp₀`.

Set `F : B.Mat k r → (ℂ →L[ℂ] ℂ)` to `fun x => ((φ₀ x : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)`. Set `π1 : B.Mat k r → (ℂ →L[ℂ] ℂ)` to `fun _ => 1`. Establish `hpsi : ∀ (w : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r), psi k r w 0 y = 1`. Introduce `w y`. Simplify using `[psi]`.

Establish `hJ : ∀ x : B.Mat k r, besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F x = ((∫ p, φ₀ (B.sgs p x) ∂D.μSS : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)`. Introduce `x`. Unfold `besselJ`. Simplify using `only [hpsi, star_one, mul_one, one_smul, π1, F]`. Rewrite using `[← integral_complex_ofReal, ← integral_smul_const]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `ext`. Simplify using `[B.sgs]`. Establish `hrep : ∀ U : Set (B.Mat k r), IsCRepOn U π1` using `fun U => ⟨rfl, fun _ _ _ _ => by ext; simp [π1]⟩`. Establish `hN` using `bessel_unipotent_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc (fun n₀ h => D.haarN.left n₀ h)`.

Establish `hU` using `bessel_unitary_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀) (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) ( …`. Establish `hs : B.sgs p₀ g = (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * ((Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r)) * (Matrix.of p₀.2.1 : B.Mat k r)` using `by show (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * (Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r) * (Matrix.of p₀.2.1 : B.Mat k r) = _`. Simplify using `only [Matrix.mul_assoc]`. Establish `key : besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F (B.sgs p₀ g) = besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F g`. Rewrite using `[hs, hU _ _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3, hN _ _ (WeylGroupFacts.mem_n_inv h2) _ h4]`.

Use `ext`. Simplify using `[π1, hpsi]`. Rewrite `key` using `[hJ, hJ]`. Use `congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) key` as an intermediate fact. Simplify using `at this`.

Conclude with `this` after adjusting the coercions.
-/
theorem averaging_invariance_holds : ACInv := by
  intro k r Wp Wq _ _ _ _ D φ₀ _hφ p₀ hp₀ g
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨h1, h2, h3, h4⟩ := hp₀
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun x => ((φ₀ x : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  let π1 : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun _ => 1
  have hpsi : ∀ (w : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r), psi k r w 0 y = 1 := by
    intro w y; simp [psi]
  have hJ : ∀ x : B.Mat k r, besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F x =
      ((∫ p, φ₀ (B.sgs p x) ∂D.μSS : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
    intro x
    unfold besselJ
    simp only [hpsi, star_one, mul_one, one_smul, π1, F]
    rw [← integral_complex_ofReal, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ext
    simp [B.sgs]
  have hrep : ∀ U : Set (B.Mat k r), IsCRepOn U π1 := fun U => ⟨rfl, fun _ _ _ _ => by ext; simp [π1]⟩
  have hN := bessel_unipotent_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    (fun n₀ h => D.haarN.left n₀ h)
  have hU := bessel_unitary_equiv_holds ℂ ℂ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    D.haarW.conc D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀)
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) (hrep _) (hrep _)
  have hs : B.sgs p₀ g = (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ *
      ((Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r)) * (Matrix.of p₀.2.1 : B.Mat k r) := by
    show (Matrix.of p₀.1.1 : B.Mat k r)⁻¹ * (Matrix.of p₀.1.2 : B.Mat k r)⁻¹ * g * (Matrix.of p₀.2.2 : B.Mat k r) *
      (Matrix.of p₀.2.1 : B.Mat k r) = _
    simp only [Matrix.mul_assoc]
  have key : besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F (B.sgs p₀ g) =
      besselJ k r D.z D.z' 0 π1 π1 D.μW D.μN D.μW' F g := by
    rw [hs, hU _ _ (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1) _ h3, hN _ _ (WeylGroupFacts.mem_n_inv h2) _ h4]
    ext
    simp [π1, hpsi]
  rw [hJ, hJ] at key
  have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) key
  simp at this
  exact_mod_cast this

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
