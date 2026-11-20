import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotInertPlaceOfMem
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPrimeNotInertPlaceOfMem.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_prime_notInert_place_of_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ P.S0 → ∃ q : ℕ, q.Prime ∧ ¬ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  first | exact @GlobalTheory.FunObj.SqNum.exists_prime_notInert_place | exact GlobalTheory.FunObj.SqNum.exists_prime_notInert_place | (intros; apply GlobalTheory.FunObj.SqNum.exists_prime_notInert_place <;> assumption)
