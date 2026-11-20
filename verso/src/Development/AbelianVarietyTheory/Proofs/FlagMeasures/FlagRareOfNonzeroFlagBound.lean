import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties

open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

/- English proof (translation)
Introduce `h`. Use `⟨⌈Real.exp 15⌉₊, ?_⟩` and prove the remaining obligations. Introduce `B p q hsig hn hq hrd hf`. Establish `hn' : Real.exp 15 ≤ (B.I.n : ℝ)` using `Nat.ceil_le.1 hn`. Establish `hn1 : 1 ≤ B.I.n`.

Establish `: 0 < ⌈Real.exp 15⌉₊` using `Nat.ceil_pos.2 (Real.exp_pos 15)`. Use linear arithmetic over natural numbers and integers. Establish `hlog : 15 ≤ Real.log B.I.n`. Use `Real.log_le_log (Real.exp_pos 15) hn'` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis.

Establish `key` using `h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf`. Establish `hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥}`. Use extensionality with `x`. Establish `hx` using `((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2`. Simplify using `only [Set.mem_ofPred_eq, ne_eq, hx, not_le]`.

Establish `hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)`. Rewrite using `[prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
