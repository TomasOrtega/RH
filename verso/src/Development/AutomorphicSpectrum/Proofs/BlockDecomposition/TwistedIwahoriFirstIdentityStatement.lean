import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentity
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Lbc.Contraction.e1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedIwahoriFirstIdentity.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.twisted_iwahori_first_identity : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.Contraction.e1 | exact GlobalTheory.CompanionTheory.Lbc.Contraction.e1 | (intros; apply GlobalTheory.CompanionTheory.Lbc.Contraction.e1 <;> assumption)
