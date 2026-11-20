import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPowPrimeMemUnitFiltrationUnitsMin.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e n : ℕ), OrdIs F p e → ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | exact GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | (intros; apply GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits <;> assumption)
