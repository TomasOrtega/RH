import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNorm
import Mathlib
open ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIsNonarchimedeanLocalFieldSpectralNorm.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_localField_structure_spectralNorm : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K], ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧ ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  first | exact @GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | exact GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | (intros; apply GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm <;> assumption)
