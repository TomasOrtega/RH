import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Equip the data with the indicated structure. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pa.BC.ps_ev :
    ∀ (R K : Type) [CommRing R] [CommRing K] (x : R →+* PowerSeries K), ∃ f : PowerSeries R →+* PowerSeries K, (∀ a, f (PowerSeries.C a) = x a) ∧ f PowerSeries.X = PowerSeries.X := by
  intro R K _ _ x
  letI : UniformSpace R := ⊥
  letI : UniformSpace K := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteUniformity K := ⟨rfl⟩
  refine ⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology
    PowerSeries.HasEval.X, ?_, ?_⟩
  · intro a
    rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
