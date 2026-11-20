import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureCompactBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurvBound.curv_entries_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCurvatureCompactBound.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.curvature_compact_bound : ∀ (e n : ℕ) (U K : Set (Fin e → ℂ)) (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), GlobalTheory.HermFrame.IsPosFrame U H₀ → IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ ξ η : Fin e → ℂ, ∑ a, ∑ b, ‖GlobalTheory.HermFrame.curv H₀ z ξ η a b‖ ≤ B * ‖ξ‖ * ‖η‖ := by
  first | exact @GlobalTheory.CurvBound.curv_entries_bound | exact GlobalTheory.CurvBound.curv_entries_bound | (intros; apply GlobalTheory.CurvBound.curv_entries_bound <;> assumption)
