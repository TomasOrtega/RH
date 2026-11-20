import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectPullbackSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSubobjectPullbackSections.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.subobject_pullback_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (D S : Subobject E) (V : X.Opens), secs ((Subobject.pullback D.arrow).obj S) V = (D.arrow.app V) ⁻¹' secs S V := by
  first | exact @GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | exact GlobalTheory.CompanionTheory.GE.secs_pullback_arrow | (intros; apply GlobalTheory.CompanionTheory.GE.secs_pullback_arrow <;> assumption)
