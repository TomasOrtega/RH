import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterBoundedConductorKillsIdeleNorms
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeCharacterBoundedConductorKillsIdeleNorms.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.heckeCharacter_bounded_conductor_kills_idele_norms : ∀ (D : D7) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (S : Finset ℕ) (k : ℕ), χ.TrivOn D.host.F → χ.HasInf (embT D) n → (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  first | exact @GlobalTheory.NormKill.chi_finIdl_norm_eq_one | exact GlobalTheory.NormKill.chi_finIdl_norm_eq_one | (intros; apply GlobalTheory.NormKill.chi_finIdl_norm_eq_one <;> assumption)
