import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetMultiplicityPosOfSocle.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos_of_socle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | exact GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | (intros; apply GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle <;> assumption)
