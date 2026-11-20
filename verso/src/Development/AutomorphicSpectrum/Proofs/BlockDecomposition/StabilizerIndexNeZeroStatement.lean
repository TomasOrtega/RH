import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStabilizerIndexNeZero.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.stabilizer_index_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G) (d : G) (f : G → ℂ),
  Continuous θ → IsCompact (K : Set G) → IsOpen (K' : Set G) → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) →
  ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * d * θ (y * k))).index ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | exact GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact | (intros; apply GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact <;> assumption)
