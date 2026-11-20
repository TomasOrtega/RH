import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTrivia
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeCont.eq_one_of_cong` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCongruenceHeckeCharacterBoundedLevelTrivia.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_congruence_heckeCharacter_bounded_level_trivial : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  first | exact @GlobalTheory.HeckeCont.eq_one_of_cong | exact GlobalTheory.HeckeCont.eq_one_of_cong | (intros; apply GlobalTheory.HeckeCont.eq_one_of_cong <;> assumption)
