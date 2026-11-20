import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProperCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNormalProperCompactification.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.exists_normal_proper_compactification : ∀ (k₀ k : Type) [Field k₀] [IsAlgClosed k₀] [Field k] (A : Type) [CommRing A] [Algebra k₀ A] (j : A →+* k) (Y : Scheme.{0}) (s : Y ⟶ Sp k₀) (a : Sp A ⟶ Y), Algebra.FiniteType k₀ A → Function.Injective j → IsProper s → a ≫ s = spMap (algebraMap k₀ A) → ∃ (W U : Scheme.{0}) (i : U ⟶ W) (π : U ⟶ Sp A) (b : W ⟶ Y) (w : Sp k ⟶ U), IsIntegral W ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme W ∧ IsProper (b ≫ s) ∧ IsOpenImmersion i ∧ i ≫ b = π ≫ a ∧ w ≫ π = spMap j := by
  first | exact @GlobalTheory.NormalCompletion.exists_normal_proper | exact GlobalTheory.NormalCompletion.exists_normal_proper | (intros; apply GlobalTheory.NormalCompletion.exists_normal_proper <;> assumption)
