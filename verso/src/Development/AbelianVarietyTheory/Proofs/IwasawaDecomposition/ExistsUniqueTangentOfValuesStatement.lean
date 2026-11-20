import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TanFibre.existsUnique_tanEv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUniqueTangentOfValues.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.existsUnique_tangent_of_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  first | exact @GlobalTheory.TanFibre.existsUnique_tanEv | exact GlobalTheory.TanFibre.existsUnique_tanEv | (intros; apply GlobalTheory.TanFibre.existsUnique_tanEv <;> assumption)
