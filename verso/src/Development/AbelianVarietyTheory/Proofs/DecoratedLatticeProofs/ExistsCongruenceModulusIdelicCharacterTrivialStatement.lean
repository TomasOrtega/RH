import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCongruenceModulusIdelicCharacterTrivial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsCongruenceModulusIdelicCharacterTrivial.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitAll.char_trivial_modSet | exact GlobalTheory.HeckeSplitAll.char_trivial_modSet | (intros; apply GlobalTheory.HeckeSplitAll.char_trivial_modSet <;> assumption)
