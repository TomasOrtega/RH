import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StdCharDegOne.stdChar_placeIdem_div` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStandardAddCharPlaceIdempotentDivPrime.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.standardAddChar_placeIdempotent_div_prime : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  first | exact @GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | exact GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | (intros; apply GlobalTheory.StdCharDegOne.stdChar_placeIdem_div <;> assumption)
