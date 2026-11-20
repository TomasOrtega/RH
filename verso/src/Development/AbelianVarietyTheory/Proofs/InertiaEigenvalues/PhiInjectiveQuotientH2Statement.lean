import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NatQuot.phi_quot_pow_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPhiInjectiveQuotientH2.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.phi_injective_quotient_H2 : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G], PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  first | exact @GlobalTheory.NatQuot.phi_quot_pow_injective | exact GlobalTheory.NatQuot.phi_quot_pow_injective | (intros; apply GlobalTheory.NatQuot.phi_quot_pow_injective <;> assumption)
