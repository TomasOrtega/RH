import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsElementSamePrimeCount
import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FExistsElementSamePrimeCount.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_element_same_prime_count : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ → ∃ x ∈ I, x ≠ 0 ∧ (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | exact GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq <;> assumption)
