import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCompactNormalNoetherianOfFlagCellCover.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  first | exact @GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | exact GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | (intros; apply GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells <;> assumption)
