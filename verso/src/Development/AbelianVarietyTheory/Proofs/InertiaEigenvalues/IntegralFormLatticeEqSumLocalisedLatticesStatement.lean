import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatSplit.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIntegralFormLatticeEqSumLocalisedLattices.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.integralFormLattice_eq_sum_localised_lattices : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w, y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i), (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  first | exact @GlobalTheory.LatSplit.main | exact GlobalTheory.LatSplit.main | (intros; apply GlobalTheory.LatSplit.main <;> assumption)
