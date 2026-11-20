import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartTestPoint
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FHodgeTateChartTestPoint.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.hodge_tate_chart_test_point : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints | exact GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints <;> assumption)
