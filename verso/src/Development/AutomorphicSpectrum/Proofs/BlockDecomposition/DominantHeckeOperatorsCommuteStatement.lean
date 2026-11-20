import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommute
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDominantHeckeOperatorsCommute.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.dominant_hecke_operators_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  first | exact @GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | exact GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | (intros; apply GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute <;> assumption)
