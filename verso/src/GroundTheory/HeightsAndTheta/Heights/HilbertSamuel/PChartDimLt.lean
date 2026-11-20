import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ J e p hJ hdim`. Establish `key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes, ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e`. Introduce `Z hZ`. Establish `: Z.IsPrime` using `hZ.1.1`. Take `⟨s, hs, hle⟩` from `ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2`.

Establish `hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞)` using `lt_of_le_of_lt hle hdim`. Establish `hlt' : s + Fintype.card K < e + Fintype.card K` using `by exact_mod_cast hlt`. Conclude with `⟨s, hs, by omega⟩`. Consider the cases of `e with`. Consider the case `zero`.

Use `lt_of_le_of_lt (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_) (WithBot.bot_lt_coe _)` and prove the remaining obligations. Take `⟨s, -, hs⟩` from `key Z hZ`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n`. Establish `hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞)` using `by exact_mod_cast Nat.lt_succ_self n`.

Use `lt_of_le_of_lt (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _ fun Z hZ => ?_) hn` and prove the remaining obligations. Take `⟨s, hs, hsn⟩` from `key Z hZ`. Rewrite using `[hs]`. Conclude with `(by omega : s ≤ n)` after adjusting the coercions.
-/
theorem ChartDimLt.proof : ChartDimLt.Statement := by
  intro K _ ι _ J e p hJ hdim
  have key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes,
      ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e := by
    intro Z hZ
    have : Z.IsPrime := hZ.1.1
    obtain ⟨s, hs, hle⟩ := ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2
    have hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt hle hdim
    have hlt' : s + Fintype.card K < e + Fintype.card K := by exact_mod_cast hlt
    exact ⟨s, hs, by omega⟩
  cases e with
  | zero =>
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_)
      (WithBot.bot_lt_coe _)
    obtain ⟨s, -, hs⟩ := key Z hZ
    omega
  | succ n =>
    have hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _
        fun Z hZ => ?_) hn
    obtain ⟨s, hs, hsn⟩ := key Z hZ
    rw [hs]
    exact_mod_cast (by omega : s ≤ n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
