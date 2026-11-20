import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalGeneralizedSpaceSpanClosed.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cuspidal_generalized_space_span_closed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1}, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | exact GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | (intros; apply GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms <;> assumption)
