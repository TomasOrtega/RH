import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

/- English proof (translation)
Establish `hmem : x ^ (b - a) ∈ unitCong (ϖ ^ e)` using `by show valuation k ((x ^ (b - a) : kˣ) : k) = 1 ∧ valuation k (((x ^ (b - a) : kˣ) : k) - 1) ≤ valuation k ((ϖ ^ e : kˣ) : k)`. Establish `hfac : (x : k) ^ b - (x : k) ^ a = (x : k) ^ a * ((x : k) ^ (b - a) - 1)`. Rewrite using `[mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]`. Rewrite `h` using `[hfac, map_mul, map_pow, hx, one_pow, one_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hx, one_pow]`. Rewrite using `[Units.val_pow_eq_pow_val]`. Conclude with `h`. Rewrite using `[← map_pow]`. Conclude with `hν _ hmem`.
-/
private theorem UpperTheory.pow_sub_eq_one_of_condLE_valuation_le {k : Type} [Field k] [ValuativeRel k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ)
    (hν : CondLE ϖ e ν) (x : kˣ) (hx : valuation k (x : k) = 1) (a b : ℕ) (hab : a < b)
    (h : valuation k ((x : k) ^ b - (x : k) ^ a) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ν x ^ (b - a) = 1 := by
  have hmem : x ^ (b - a) ∈ unitCong (ϖ ^ e) := by
    show valuation k ((x ^ (b - a) : kˣ) : k) = 1 ∧
      valuation k (((x ^ (b - a) : kˣ) : k) - 1) ≤ valuation k ((ϖ ^ e : kˣ) : k)
    have hfac : (x : k) ^ b - (x : k) ^ a = (x : k) ^ a * ((x : k) ^ (b - a) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one]
    rw [hfac, map_mul, map_pow, hx, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
    · rw [Units.val_pow_eq_pow_val]
      exact h
  rw [← map_pow]
  exact hν _ hmem

/- English proof (translation)
Introduce `k _ _ _ _ ϖ e ν hϖ hν x hx`. Establish `hpow : ∀ n : ℕ, (x : k) ^ n ∈ 𝒪[k]` using `fun n => (Valuation.mem_integer_iff _ _).2 (by rw [map_pow, hx, one_pow])`. Set `g : ℕ → Res k e` to `fun n => Ideal.Quotient.mk _ ⟨(x : k) ^ n, hpow n⟩`. Take `⟨i, j, hne, hg⟩` from `Finite.exists_ne_map_eq_of_infinite g`. Establish `key : ∀ a b : ℕ, a < b → g a = g b → IsIntegral ℤ (ν x : ℂ)`.

Introduce `a b hab h`. Establish `h1` using `Ideal.Quotient.eq.1 h.symm`. Establish `h2` using `(Model.val_le_iff_mem hϖ e _).1 h1`. Establish `h3 : ν x ^ (b - a) = 1` using `UpperTheory.pow_sub_eq_one_of_condLE_valuation_le ϖ e ν hν x hx a b hab (by simpa using h2)`. Use `IsIntegral.of_pow (Nat.sub_pos_of_lt hab) ?_` and prove the remaining obligations.

Rewrite using `[← Units.val_pow_eq_pow_val, h3, Units.val_one]`. Conclude with `isIntegral_one`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Conclude with `key i j h hg`. Conclude with `key j i h hg.symm`.
-/
theorem UpperTheory.isIntegral_unitChar_of_conductor_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (e : ℕ) (ν : kˣ →* ℂˣ), IsUnif ϖ → CondLE ϖ e ν → ∀ x : kˣ, valuation k (x : k) = 1 → IsIntegral ℤ (ν x : ℂ) := by
  intro k _ _ _ _ ϖ e ν hϖ hν x hx
  have hpow : ∀ n : ℕ, (x : k) ^ n ∈ 𝒪[k] := fun n =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_pow, hx, one_pow])
  let g : ℕ → Res k e := fun n => Ideal.Quotient.mk _ ⟨(x : k) ^ n, hpow n⟩
  obtain ⟨i, j, hne, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → IsIntegral ℤ (ν x : ℂ) := by
    intro a b hab h
    have h1 := Ideal.Quotient.eq.1 h.symm
    have h2 := (Model.val_le_iff_mem hϖ e _).1 h1
    have h3 : ν x ^ (b - a) = 1 := UpperTheory.pow_sub_eq_one_of_condLE_valuation_le ϖ e ν hν x hx a b hab (by simpa using h2)
    refine IsIntegral.of_pow (Nat.sub_pos_of_lt hab) ?_
    rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    exact isIntegral_one
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hg
  · exact key j i h hg.symm
