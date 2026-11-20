import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibre
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemBasicOpenNormCoeffOfFibre.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] {V : X.Opens} (hV : IsAffineOpen V)
    [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X), x ∈ V →
    (∀ y : Y, f y = x → y ∈ Y.basicOpen τ) →
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  first | exact @GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | exact GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre | (intros; apply GlobalTheory.NormalDescent.mem_basicOpen_normCoeff_of_fibre <;> assumption)
