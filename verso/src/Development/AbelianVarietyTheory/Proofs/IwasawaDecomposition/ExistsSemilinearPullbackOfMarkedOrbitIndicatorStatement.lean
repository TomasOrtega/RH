import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsSemilinearPullbackOfMarkedOrbitIndicator.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one <;> assumption)
