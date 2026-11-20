import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.T2SpaceLatticeVOfGoodSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ZlWCbInjective
import Formalism.SharpRestriction.LevelLetterCocycles.NormLtOneIffToZMod

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation Topology Filter

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zetaQ_pow (P : LocPrime l) (j k : ℕ) : P.ζQ (j + k) ^ (l ^ k) = P.ζQ j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Establish `hroot : P.ζQ 1 ^ l = 1`. Establish `h0` using `zetaQ_pow P 0 1`. Rewrite `h0` using `[zero_add, P.ζQ_zero, pow_one]`. Then use the resulting hypothesis. Establish `hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1`. Introduce `g`.

Take `⟨a, ha, -⟩` from `P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])`. Establish `hA : ‖(a : ℚ_[l])‖ ≤ 1`. Establish `h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ))` using `by first`. Consider the case `exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)`. Consider the case `exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)`.

Simplify using `using h2`. Establish `hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1`. Establish `h3 : (1 : ℝ) ≤ l` using `by exact_mod_cast hl.out.one_lt.le`. Simplify using `only [Nat.cast_one, zpow_neg, zpow_one]`. Use `first`.

Consider the case `exact inv_le_one_of_one_le₀ h3`. Consider the case `exact inv_le_one h3`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact Padic.nonarchimedean _ _`. Consider the case `exact padicNormE.nonarchimedean _ _`.

Consider the case `exact IsUltrametricDist.norm_add_le_max _ _`. Use `_ ≤ 1 := max_le (ha.trans hl1) hA`. Establish `h1` using `hle h`. Establish `h2` using `hle h⁻¹`. Establish `hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1`.

Rewrite using `[← norm_mul, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules. Conclude with `le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])`.
-/
theorem chiQ_norm (P : LocPrime l) (h : GQ l) : ‖(P.χQ h : ℚ_[l])‖ = 1 := by
  have hroot : P.ζQ 1 ^ l = 1 := by
    have h0 := zetaQ_pow P 0 1
    rwa [zero_add, P.ζQ_zero, pow_one] at h0
  have hle : ∀ g : GQ l, ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    intro g
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 1 (P.ζQ 1) (by rwa [pow_one])
    have hA : ‖(a : ℚ_[l])‖ ≤ 1 := by
      have h2 : ‖((a : ℤ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((0 : ℕ) : ℤ)) := by
        first
          | exact (Padic.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
          | exact (padicNormE.norm_int_le_pow_iff_dvd (a : ℤ) 0).2 (by simp)
      simpa using h2
    have hl1 : (l : ℝ) ^ (-((1 : ℕ) : ℤ)) ≤ 1 := by
      have h3 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
      simp only [Nat.cast_one, zpow_neg, zpow_one]
      first
        | exact inv_le_one_of_one_le₀ h3
        | exact inv_le_one h3
    calc ‖(P.χQ g : ℚ_[l])‖ = ‖((P.χQ g : ℚ_[l]) - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ max ‖(P.χQ g : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := by
        first
          | exact Padic.nonarchimedean _ _
          | exact padicNormE.nonarchimedean _ _
          | exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha.trans hl1) hA
  have h1 := hle h
  have h2 := hle h⁻¹
  have hmul : ‖(P.χQ h : ℚ_[l])‖ * ‖(P.χQ h⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]
    simp
  exact le_antisymm h1 (by nlinarith [norm_nonneg (P.χQ h : ℚ_[l]), norm_nonneg (P.χQ h⁻¹ : ℚ_[l])])

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
