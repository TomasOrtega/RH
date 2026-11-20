import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvelopingAlgebraLineWords
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorFin.WordSpan.exists_wop_of_mem_adjoin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEnvelopingAlgebraLineWords.lean&line=121#L121)
-/
theorem _root_.GlobalTheory.T.enveloping_algebra_line_words : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), ∃ z : List (ℝ → G) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧ ∀ f : smLoc J s, (T f).1 = wop z f.1 := by
  first | exact @GlobalTheory.TorFin.WordSpan.exists_wop_of_mem_adjoin | exact GlobalTheory.TorFin.WordSpan.exists_wop_of_mem_adjoin | (intros; apply GlobalTheory.TorFin.WordSpan.exists_wop_of_mem_adjoin <;> assumption)
