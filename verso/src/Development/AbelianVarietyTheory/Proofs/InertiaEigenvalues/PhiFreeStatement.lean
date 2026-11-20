import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cyc.phi_free` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPhiFree.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  first | exact @GlobalTheory.Cyc.phi_free | exact GlobalTheory.Cyc.phi_free | (intros; apply GlobalTheory.Cyc.phi_free <;> assumption)
