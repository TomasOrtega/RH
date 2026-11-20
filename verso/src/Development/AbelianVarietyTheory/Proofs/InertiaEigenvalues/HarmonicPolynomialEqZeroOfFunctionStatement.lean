import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarmonicPolynomialEqZeroOfFunction.lean&line=516#L516)
-/
theorem _root_.GlobalTheory.T.harmonic_polynomial_eq_zero_of_function : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  first | exact @GlobalTheory.ExportSeries.HarmInj.harm_inj | exact GlobalTheory.ExportSeries.HarmInj.harm_inj | (intros; apply GlobalTheory.ExportSeries.HarmInj.harm_inj <;> assumption)
