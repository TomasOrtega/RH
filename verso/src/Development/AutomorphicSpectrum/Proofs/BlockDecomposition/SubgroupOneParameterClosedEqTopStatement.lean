import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubgroupOneParameterClosedEqTop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSubgroupOneParameterClosedEqTop.lean&line=182#L182)
-/
theorem _root_.GlobalTheory.T.subgroup_one_parameter_closed_eq_top : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Subgroup (GL (Fin a) (Cinf E))), (∀ (c : ℝ → GL (Fin a) (Cinf E)) (X : GlobalTheory.CuspRep.Lie E a), Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → HasDerivAt (fun t => toL (c t).val) X 0 → ∀ t, c t ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | exact GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf | (intros; apply GlobalTheory.CompanionTheory.GenOneParam.eq_top_of_oneParam_Cinf <;> assumption)
