import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHypothesesPreservedByLinearPullback.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.hypotheses_preserved_by_linear_pullback : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull <;> assumption)
