import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpen
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FGeneralLinearIntegralCompactOpen.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.generalLinear_integral_compact_open : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧ LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧ IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.gl_topology | exact GlobalTheory.CompanionTheory.QLTop.gl_topology | (intros; apply GlobalTheory.CompanionTheory.QLTop.gl_topology <;> assumption)
