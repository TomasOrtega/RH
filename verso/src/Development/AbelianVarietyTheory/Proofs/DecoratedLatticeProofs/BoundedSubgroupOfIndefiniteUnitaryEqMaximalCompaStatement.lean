import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedSubgroupOfIndefiniteUnitaryEqMaximalCompa
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoundedUnitary.eq_Kset_of_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FBoundedSubgroupOfIndefiniteUnitaryEqMaximalCompa.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.bounded_subgroup_of_indefinite_unitary_eq_maximalCompact : ∀ (n : ℕ) (ε : Fin n → Bool) (G' : Set (Matrix (Fin n) (Fin n) ℂ)), G' ⊆ Formalism.MainNotions.S.UJset ε → Formalism.REAL.Kset ε ⊆ G' → (∀ a ∈ G', ∀ b ∈ G', a * b ∈ G') → (∀ a ∈ G', a⁻¹ ∈ G') → (∃ C : ℝ, ∀ a ∈ G', ∀ i j, ‖a i j‖ ≤ C) → G' = Formalism.REAL.Kset ε := by
  first | exact @GlobalTheory.BoundedUnitary.eq_Kset_of_bounded | exact GlobalTheory.BoundedUnitary.eq_Kset_of_bounded | (intros; apply GlobalTheory.BoundedUnitary.eq_Kset_of_bounded <;> assumption)
