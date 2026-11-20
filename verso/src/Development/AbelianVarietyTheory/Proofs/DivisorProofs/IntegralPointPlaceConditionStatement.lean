import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceCondition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralPointPlaceCondition.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.integral_point_place_condition : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (U : V.X.Opens) (g : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) g) → (∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal → z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) → ∀ x ∈ U, (l : 𝓞 F) ∈ (V.p x).asIdeal → RegAt x g := by
  first | exact @GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | exact GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over | (intros; apply GlobalTheory.HtGen.RegOver.regAt_of_integral_values_over <;> assumption)
