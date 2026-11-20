import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfChernClassesOfRootsEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemSpanOfChernClassesOfRootsEqZero.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.mem_span_of_chernClassesOfRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ), chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪ {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  first | exact @GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | exact GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | (intros; apply GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero <;> assumption)
