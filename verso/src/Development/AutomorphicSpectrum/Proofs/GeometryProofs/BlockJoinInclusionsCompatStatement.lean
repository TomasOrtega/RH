import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBlockJoinInclusionsCompat.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.block_join_inclusions_compat : (∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (Ω : Type) (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω), IsBlockMap Sum.inl (joinInl ι₁ ι₂) ∧ IsBlockMap Sum.inr (joinInr ι₁ ι₂) ∧ joinVec y₁ y₂ ∘ joinInl ι₁ ι₂ = y₁ ∧ joinVec y₁ y₂ ∘ joinInr ι₁ ι₂ = y₂) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] (y : (Σ k, ι' k) → Ω), IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)) ∧ (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (K'' : Type) [Fintype K''] (ι'' : K'' → Type) [∀ k, Fintype (ι'' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (κ' : K' → K'') (v' : (Σ k, ι' k) → Σ k, ι'' k), IsBlockMap κ v → IsBlockMap κ' v' → IsBlockMap (κ' ∘ κ) (v' ∘ v) ∧ ∀ a, pullDeg (κ' ∘ κ) a = pullDeg κ' (pullDeg κ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | exact GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.join_block_maps <;> assumption)
