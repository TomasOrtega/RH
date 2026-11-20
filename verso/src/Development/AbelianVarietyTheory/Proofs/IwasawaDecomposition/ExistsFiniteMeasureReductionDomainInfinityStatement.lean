import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteMeasureReductionDomainInfinity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLInfReduction.exists_cover_of_finite_measure` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsFiniteMeasureReductionDomainInfinity.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_finite_measure_reduction_domain_infinity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)), Submodule.IsLattice E Λ → ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure], ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E, (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧ ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  first | exact @GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | exact GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | (intros; apply GlobalTheory.GLInfReduction.exists_cover_of_finite_measure <;> assumption)
