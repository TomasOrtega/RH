import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamLatticeTangentCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.Pad.latDR_comb_act` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeRhamLatticeTangentCombination.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.de_rham_lattice_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X) (w : Sp (DualNumber C) ⟶ t.G.left), IsTanAtG t x w → w ∈ latDR t x → ∀ (n : ℕ) (a : Fin n → 𝓞 E) (c : Fin n → C), (∀ j, ‖c j‖ ≤ 1) → ∀ W : Sp (DualNumber C) ⟶ t.G.left, IsCombAtG t x (fun j => w ≫ (t.act.act (a j)).left) c W → W ∈ latDR t x := by
  first | exact @GlobalTheory.ShFam.Pad.latDR_comb_act | exact GlobalTheory.ShFam.Pad.latDR_comb_act | (intros; apply GlobalTheory.ShFam.Pad.latDR_comb_act <;> assumption)
