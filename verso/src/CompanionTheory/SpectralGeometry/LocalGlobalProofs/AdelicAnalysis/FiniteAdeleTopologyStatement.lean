import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FFiniteAdeleTopology.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | exact GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology | (intros; apply GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology <;> assumption)
