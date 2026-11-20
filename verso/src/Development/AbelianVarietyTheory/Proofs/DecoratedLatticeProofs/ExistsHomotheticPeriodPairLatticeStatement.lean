import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsHomotheticPeriodPairLattice.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_homothetic_periodPair_lattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair, (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧ (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧ L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  first | exact @GlobalTheory.homotheticLattice | exact GlobalTheory.homotheticLattice | (intros; apply GlobalTheory.homotheticLattice <;> assumption)
