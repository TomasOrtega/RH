import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRegularValuesInAdjoinedField.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.regular_values_in_adjoined_field : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | exact GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification <;> assumption)
