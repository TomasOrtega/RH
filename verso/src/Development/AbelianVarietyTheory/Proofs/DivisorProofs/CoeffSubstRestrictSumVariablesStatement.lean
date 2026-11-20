import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffSubstRestrictSumVariables.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.coeff_subst_restrict_sum_variables : ∀ {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ] (g : MvPowerSeries (ι ⊕ κ) R), (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) = coeff (α.mapDomain Sum.inl) g) ∧ (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) = coeff (α.mapDomain Sum.inr) g) := by
  first | exact @GlobalTheory.coeff_subst_restrict_sum | exact GlobalTheory.coeff_subst_restrict_sum | (intros; apply GlobalTheory.coeff_subst_restrict_sum <;> assumption)
