import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder`. Establish `hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2` using `(GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc`. Establish `hI` using `hf.integral_hasStrictDerivAt 0 0`. Establish `hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) = fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2`. Use function extensionality and compare the values at `t`.

Rewrite using `[← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]`. Normalize the expressions using the abelian group laws. Rewrite using `[hE]`. Establish `h` using `hI.hasDerivAt.add_const hφ.toL2`. Simplify `h` using `[hc0]`.
-/
theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
