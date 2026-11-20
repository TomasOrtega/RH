import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FMemIntegralGLIffIntegralUnitDet.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.mem_integralGL_iff_integral_unit_det : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | exact GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | (intros; apply GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff <;> assumption)
