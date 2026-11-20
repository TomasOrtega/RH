import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealMapOfGermsAffineScheme
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemIdealMapOfGermsAffineScheme.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.mem_ideal_map_of_germs_affineScheme : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)), (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) → s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  first | exact @GlobalTheory.GermAff.mem_map_of_germ | exact GlobalTheory.GermAff.mem_map_of_germ | (intros; apply GlobalTheory.GermAff.mem_map_of_germ <;> assumption)
