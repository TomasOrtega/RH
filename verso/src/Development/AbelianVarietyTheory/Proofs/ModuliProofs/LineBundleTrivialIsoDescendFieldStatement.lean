import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
/- English proof (citation)
Apply `GlobalTheory.lb_gen_iso_descend_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FLineBundleTrivialIsoDescendField.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.lineBundle_trivial_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  first | exact @GlobalTheory.lb_gen_iso_descend_field | exact GlobalTheory.lb_gen_iso_descend_field | (intros; apply GlobalTheory.lb_gen_iso_descend_field <;> assumption)
