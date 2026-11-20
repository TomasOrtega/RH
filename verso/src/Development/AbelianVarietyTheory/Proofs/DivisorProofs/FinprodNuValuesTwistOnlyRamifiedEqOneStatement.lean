import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwistPairs.finprod_val_nu_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinprodNuValuesTwistOnlyRamifiedEqOne.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.finprod_nu_values_twist_only_ramified_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E)) (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  first | exact @GlobalTheory.TwistPairs.finprod_val_nu_eq_one | exact GlobalTheory.TwistPairs.finprod_val_nu_eq_one | (intros; apply GlobalTheory.TwistPairs.finprod_val_nu_eq_one <;> assumption)
