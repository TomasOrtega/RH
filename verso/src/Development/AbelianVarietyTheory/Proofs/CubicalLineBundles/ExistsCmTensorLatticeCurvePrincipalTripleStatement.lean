import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTriple
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CM.exists_isTen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FExistsCmTensorLatticeCurvePrincipalTriple.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  first | exact @GlobalTheory.CM.exists_isTen | exact GlobalTheory.CM.exists_isTen | (intros; apply GlobalTheory.CM.exists_isTen <;> assumption)
