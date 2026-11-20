import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsCuspidalListHarishChandraPairingNeZero.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ), IsIrr χ → ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.SuppCusp.exists_cusp_list | exact GlobalTheory.GLq.SuppCusp.exists_cusp_list | (intros; apply GlobalTheory.GLq.SuppCusp.exists_cusp_list <;> assumption)
