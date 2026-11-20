import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.IndIrr
import Development.WeilBound.CoreStatements.RegularisedThetaMirabolic.CuspidalMirabolic.IndDim

noncomputable section

open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling

namespace PositivityTheory.Mirab

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mirabInduced_isIrreducible (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) : (mirabInduced n ψ₀).IsIrreducible := by
  exact PositivityTheory.Mirab.Irr.mirabInduced_isIrreducible n ψ₀ hψ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finrank_mirabInducedSpace_eq_index (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = (uniSub k n).index := by
  exact PositivityTheory.Mirab.Dim.finrank_mirabInducedSpace_eq_index n ψ₀

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem index_uniSub : (uniSub k n).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  exact PositivityTheory.Mirab.Dim.index_uniSub n

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_mirabInducedSpace (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  rw [finrank_mirabInducedSpace_eq_index, index_uniSub]

end PositivityTheory.Mirab
