import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleSupportedAtPlaceNotIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.FinPl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.NotIntAt.exists_not_intAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsAdeleSupportedAtPlaceNotIntegral.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_adele_supportedAt_place_not_integral : ∀ (D : D7) (v : Pl D), ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.NotIntAt.exists_not_intAt | exact GlobalTheory.FinPl.NotIntAt.exists_not_intAt | (intros; apply GlobalTheory.FinPl.NotIntAt.exists_not_intAt <;> assumption)
