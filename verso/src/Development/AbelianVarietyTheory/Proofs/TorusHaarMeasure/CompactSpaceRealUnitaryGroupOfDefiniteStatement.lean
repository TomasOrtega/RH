import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
/- English proof (citation)
Apply `GlobalTheory.FinCovol.compactSpace_unitary_of_definite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTorusHaarMeasure%2FCompactSpaceRealUnitaryGroupOfDefinite.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  first | exact @GlobalTheory.FinCovol.compactSpace_unitary_of_definite | exact GlobalTheory.FinCovol.compactSpace_unitary_of_definite | (intros; apply GlobalTheory.FinCovol.compactSpace_unitary_of_definite <;> assumption)
