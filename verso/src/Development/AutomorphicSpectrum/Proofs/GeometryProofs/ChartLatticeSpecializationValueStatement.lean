import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FChartLatticeSpecializationValue.lean&line=147#L147)
-/
theorem _root_.GlobalTheory.T.chart_lattice_specialization_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet <;> assumption)
