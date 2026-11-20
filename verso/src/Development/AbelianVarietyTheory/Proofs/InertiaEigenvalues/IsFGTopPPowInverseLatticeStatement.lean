import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFGTopPPowInverseLattice
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isFGTop_comap_lsmul_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsFGTopPPowInverseLattice.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.isFGTop_p_pow_inverse_lattice : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  first | exact @GlobalTheory.isFGTop_comap_lsmul_one | exact GlobalTheory.isFGTop_comap_lsmul_one | (intros; apply GlobalTheory.isFGTop_comap_lsmul_one <;> assumption)
