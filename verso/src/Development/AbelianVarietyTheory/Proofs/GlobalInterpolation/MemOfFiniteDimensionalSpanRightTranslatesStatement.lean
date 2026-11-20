import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemOfFiniteDimensionalSpanRightTranslates
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FMemOfFiniteDimensionalSpanRightTranslates.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  first | exact @GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | exact GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | (intros; apply GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates <;> assumption)
