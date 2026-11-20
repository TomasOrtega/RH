import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FJoinModelPointsProject.lean&line=294#L294)
-/
theorem _root_.GlobalTheory.T.join_model_points_project : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω), IsArithVar (mCoordIdeal (joinOf M R i)) (dimFl Ψ N + 1) ∧ Birational (joinOf M R i) ∧ (∀ (L : Type) [Field L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) ∈ ptsOver L M.P ∧ (fun p => z (joinInr M.ι R.ι p)) ∈ ptsOver L R.P) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L], ∀ w ∈ ptsOver L M.P, ∃ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | exact GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main <;> assumption)
