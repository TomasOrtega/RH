import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ _`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w a b ha hb`. Conclude with `Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb`. Introduce `w m d hd hmd`.

Take `⟨k, rfl⟩` from `hmd`. Establish `hm0 : m ≠ 0` using `by rintro rfl; simp at hd`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hd`. Establish `hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K)`. Introduce `n`.

Establish `h` using `Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)`. Simplify using `using h`. Use `⟨hnn m, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]`. Combine the linear relations using `[hnn k]`.

Introduce `d hd`. Establish `hf` using `FractionalIdeal.finite_factors (K := K) (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))`. Rewrite `hf` using `[Filter.eventually_cofinite]`. Use `hf.subset ?_` and prove the remaining obligations. Introduce `w hw`.

Conclude with `hw`. Introduce `d hd s`. Conclude with `Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'`.
-/
theorem vw_lw_arith : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  intro K _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w a b ha hb
    exact Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb
  · intro w m d hd hmd
    obtain ⟨k, rfl⟩ := hmd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    have hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K) := by
      intro n
      have h := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)
      simpa using h
    refine ⟨hnn m, ?_⟩
    rw [Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
    linarith [hnn k]
  · intro d hd
    have hf := FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    exact hw
  · intro d hd s
    exact Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'

end GlobalTheory
