import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
/- English proof (translation)
Introduce `R K _ _ x`. Use `letI : UniformSpace R := ⊥`. Use `letI : UniformSpace K := ⊥`. Use `haveI : DiscreteUniformity R := ⟨rfl⟩`. Use `haveI : DiscreteUniformity K := ⟨rfl⟩`.

Use `⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology PowerSeries.HasEval.X, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]`. Rewrite using `[PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]`.
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
