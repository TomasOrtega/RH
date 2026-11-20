import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsIsoOnGeometricFibresOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.isIso_of_isIso_fibres` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIsoOfIsIsoOnGeometricFibresOfSmooth.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.isIso_of_isIso_on_geometric_fibres_of_smooth : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → (∀ s : T, ∃ (Ω : Type) (_ : Field Ω) (x : Sp Ω ⟶ T), s ∈ Set.range x ∧ IsIso (pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp))) → IsIso h := by
  first | exact @GlobalTheory.Mum.isIso_of_isIso_fibres | exact GlobalTheory.Mum.isIso_of_isIso_fibres | (intros; apply GlobalTheory.Mum.isIso_of_isIso_fibres <;> assumption)
