import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `k H _ _ _ _ n j hn`. Establish `hdim : Module.finrank k H = Module.finrank k (Fin n → k)` using `by simp [hn]`. Set `e : H ≃ₗ[k] (Fin n → k)` to `LinearEquiv.ofFinrankEq H (Fin n → k) hdim`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `(Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_` and prove the remaining obligations.

Introduce `D`. Express the relevant statement in the definitionally equal form `Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j`. Rewrite using `[LinearEquiv.finrank_map_eq]`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.grCard_of :
    GrCard := by
  intro k H _ _ _ _ n j hn
  have hdim : Module.finrank k H = Module.finrank k (Fin n → k) := by simp [hn]
  let e : H ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq H (Fin n → k) hdim
  apply Nat.card_congr
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro D
  change Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j
  rw [LinearEquiv.finrank_map_eq]
