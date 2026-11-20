import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowPSmulMemOneFractionRing
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.padicCoeff_exists_pow_smul_mem_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPowPSmulMemOneFractionRing.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_pow_p_smul_mem_one_fractionRing : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  first | exact @GlobalTheory.padicCoeff_exists_pow_smul_mem_one | exact GlobalTheory.padicCoeff_exists_pow_smul_mem_one | (intros; apply GlobalTheory.padicCoeff_exists_pow_smul_mem_one <;> assumption)
