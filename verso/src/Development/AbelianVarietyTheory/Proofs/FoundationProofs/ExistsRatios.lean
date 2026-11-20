import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square.Ratio

open Formalism.DivisionValues.ValuationRepresentative (vw_mul vw_inv)

/- English proof (translation)
Take `⟨a, k, k', hd, hx⟩` from `h`. Establish `hQk : ∀ k, (Qn : 𝓞 K) ^ k ∉ w.asIdeal` using `fun k h => hQ (w.isPrime.mem_of_pow_mem k h)`. Establish `ha : a ∉ w.asIdeal` using `fun h => hQk k' (Ideal.mem_of_dvd _ hd h)`. Establish `ha0 : (a : K) ≠ 0`. Introduce `h`.

Apply `ha` to reduce the goal to its premises. Establish `: a = 0` using `by exact_mod_cast h`. Rewrite using `[this]`. Conclude with `zero_mem _`. Rewrite `ha0` using `[← hx]`.

Establish `h1` using `Formalism.DivisionValues.ReductionFirst.vw_unit w a ha`. Establish `h2` using `Formalism.DivisionValues.ReductionFirst.vw_unit w _ (hQk k)`. Establish `e : (((Qn : 𝓞 K) ^ k : 𝓞 K) : K) = (Qn : K) ^ k` using `by simp`. Rewrite `h2` using `[e]`. Rewrite `h1` using `[← hx, vw_mul w _ _ (left_ne_zero_of_mul ha0) (right_ne_zero_of_mul ha0), h2]`.

Conclude with `⟨left_ne_zero_of_mul ha0, by simpa using h1⟩`.
-/
theorem away {K : Type} [Field K] [NumberField K] [StarRing K] {w : Pl K} {Qn : ℕ}
    (hQ : (Qn : 𝓞 K) ∉ w.asIdeal) {x : K} (h : IsAwayUnit Qn x) : x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', hd, hx⟩ := h
  have hQk : ∀ k, (Qn : 𝓞 K) ^ k ∉ w.asIdeal := fun k h => hQ (w.isPrime.mem_of_pow_mem k h)
  have ha : a ∉ w.asIdeal := fun h => hQk k' (Ideal.mem_of_dvd _ hd h)
  have ha0 : (a : K) ≠ 0 := by
    intro h; apply ha
    have : a = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  rw [← hx] at ha0
  have h1 := Formalism.DivisionValues.ReductionFirst.vw_unit w a ha
  have h2 := Formalism.DivisionValues.ReductionFirst.vw_unit w _ (hQk k)
  have e : (((Qn : 𝓞 K) ^ k : 𝓞 K) : K) = (Qn : K) ^ k := by simp
  rw [e] at h2
  rw [← hx, vw_mul w _ _ (left_ne_zero_of_mul ha0) (right_ne_zero_of_mul ha0), h2] at h1
  exact ⟨left_ne_zero_of_mul ha0, by simpa using h1⟩

/- English proof (translation)
Introduce `K _ _ _ σ₀ w Qn hQ e0 h he L0 L1 zT zTd zψ Ep gT n0 er hL hpos hneg`. Establish `he' : (e0 : ℤ) ≤ h` using `by exact_mod_cast he`. Establish `key : ∀ s : ℤ, 1 ≤ s → s ≤ h → zψ s ≠ 0 ∧ zψ s / zT s ≠ 0 ∧ σ₀ (zψ s / zT s) * L0 s = L1 s`. Introduce `s h1 h2`. Take `⟨hT, -, hrel, -, -⟩` from `hpos s h1 h2`.

Take `⟨-, hL1⟩` from `hL s (by omega) h2`. Establish `hT' : σ₀ (zT s) ≠ 0` using `(map_ne_zero σ₀).2 hT`. Establish `hψ : zψ s ≠ 0`. Introduce `h0`. Rewrite `hrel` using `[h0, map_zero, zero_mul]`.

Conclude with `mul_ne_zero hT' hL1 hrel.symm`. Use `⟨hψ, div_ne_zero hψ hT, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hrel`.

Use `⟨fun s => if 1 ≤ s then zψ s / zT s else Ep s * (zψ (1 - s) / zT (1 - s)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s h1 h2`. Distinguish the cases in `hs : 1 ≤ s`. Simplify using `only [hs, if_true]`. Conclude with `(key s hs h2).2`.

Simplify using `only [hs, if_false]`. Take `⟨hu, hrel⟩` from `hneg s h1 (by omega)`. Take `⟨-, hne, hk⟩` from `key (1 - s) (by omega) (by omega)`. Use `⟨mul_ne_zero (away hQ hu).1 hne, ?_⟩` and prove the remaining obligations. Establish `hL0` using `(hL (1 - s) (by omega) (by omega)).1`.

Apply `mul_right_cancel₀ hL0` to reduce the goal to its premises. Rewrite using `[hrel, map_mul, ← hk]`. Expand and normalize the polynomial expressions, which then agree. Introduce `s h1 h2`. Simplify using `only [h1, if_true]`.

Take `⟨hT, -, -, hb1, hb2⟩` from `hpos s h1 h2`. Establish `hψ` using `(key s h1 h2).1`. Establish `hv : vw w (zψ s / zT s) = vw w (zψ s) - vw w (zT s)`. Rewrite using `[div_eq_mul_inv, vw_mul w _ _ hψ (inv_ne_zero hT), vw_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hv]`. Establish `a1` using `le_abs_self ((vw w (zT s) + gT s : ℤ) : ℝ)`. Establish `a2` using `neg_abs_le ((vw w (zT s) + gT s : ℤ) : ℝ)`. Establish `a3` using `le_abs_self ((vw w (zTd s) + gT s : ℤ) : ℝ)`. Generalize the expression as in `|((vw w (zT s) + gT s : ℤ) : ℝ)| = A at *`.

Generalize the expression as in `|((vw w (zTd s) + gT s : ℤ) : ℝ)| = B at *`. Move the coercions through the operations in `at *`. Apply the tactic sequence `constructor <;> linarith`. Introduce `s h1 h2`. Establish `hs : ¬ 1 ≤ s` using `by omega`.

Establish `hs' : 1 ≤ 1 - s` using `by omega`. Simplify using `only [hs, hs', if_true, if_false]`. Take `⟨hu, -⟩` from `hneg s h1 h2`. Take `⟨hE, hv⟩` from `away hQ hu`. Rewrite using `[vw_mul w _ _ hE (key (1 - s) hs' (by omega)).2.1, hv, zero_add]`.
-/
theorem exists_ratios : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ), (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (e0 h : ℕ), e0 ≤ h → ∀ (L0 L1 : ℤ → ℂ) (zT zTd zψ Ep : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ) (er : ℝ), (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → L0 s ≠ 0 ∧ L1 s ≠ 0) → (∀ s : ℤ, 1 ≤ s → s ≤ h → zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * L0 s = σ₀ (zT s) * L1 s ∧ -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧ L1 s * L0 (1 - s) = σ₀ (Ep s) * (L1 (1 - s) * L0 s)) → ∃ ρ : ℤ → K, (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ h → ρ s ≠ 0 ∧ σ₀ (ρ s) * L0 s = L1 s) ∧ (∀ s : ℤ, 1 ≤ s → s ≤ h → (vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + |((vw w (zTd s) + gT s : ℤ) : ℝ)| + er ∧ -(vw w (ρ s) : ℝ) ≤ |((vw w (zT s) + gT s : ℤ) : ℝ)| + n0 s) ∧ (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) := by
  intro K _ _ _ σ₀ w Qn hQ e0 h he L0 L1 zT zTd zψ Ep gT n0 er hL hpos hneg
  have he' : (e0 : ℤ) ≤ h := by exact_mod_cast he
  have key : ∀ s : ℤ, 1 ≤ s → s ≤ h → zψ s ≠ 0 ∧ zψ s / zT s ≠ 0 ∧
      σ₀ (zψ s / zT s) * L0 s = L1 s := by
    intro s h1 h2
    obtain ⟨hT, -, hrel, -, -⟩ := hpos s h1 h2
    obtain ⟨-, hL1⟩ := hL s (by omega) h2
    have hT' : σ₀ (zT s) ≠ 0 := (map_ne_zero σ₀).2 hT
    have hψ : zψ s ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact mul_ne_zero hT' hL1 hrel.symm
    refine ⟨hψ, div_ne_zero hψ hT, ?_⟩
    rw [map_div₀]
    field_simp
    linear_combination hrel
  refine ⟨fun s => if 1 ≤ s then zψ s / zT s else Ep s * (zψ (1 - s) / zT (1 - s)), ?_, ?_, ?_⟩
  · intro s h1 h2
    by_cases hs : 1 ≤ s
    · simp only [hs, if_true]
      exact (key s hs h2).2
    · simp only [hs, if_false]
      obtain ⟨hu, hrel⟩ := hneg s h1 (by omega)
      obtain ⟨-, hne, hk⟩ := key (1 - s) (by omega) (by omega)
      refine ⟨mul_ne_zero (away hQ hu).1 hne, ?_⟩
      have hL0 := (hL (1 - s) (by omega) (by omega)).1
      apply mul_right_cancel₀ hL0
      rw [hrel, map_mul, ← hk]
      ring
  · intro s h1 h2
    simp only [h1, if_true]
    obtain ⟨hT, -, -, hb1, hb2⟩ := hpos s h1 h2
    have hψ := (key s h1 h2).1
    have hv : vw w (zψ s / zT s) = vw w (zψ s) - vw w (zT s) := by
      rw [div_eq_mul_inv, vw_mul w _ _ hψ (inv_ne_zero hT), vw_inv]; ring
    rw [hv]
    have a1 := le_abs_self ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a2 := neg_abs_le ((vw w (zT s) + gT s : ℤ) : ℝ)
    have a3 := le_abs_self ((vw w (zTd s) + gT s : ℤ) : ℝ)
    generalize |((vw w (zT s) + gT s : ℤ) : ℝ)| = A at *
    generalize |((vw w (zTd s) + gT s : ℤ) : ℝ)| = B at *
    push_cast at *
    constructor <;> linarith
  · intro s h1 h2
    have hs : ¬ 1 ≤ s := by omega
    have hs' : 1 ≤ 1 - s := by omega
    simp only [hs, hs', if_true, if_false]
    obtain ⟨hu, -⟩ := hneg s h1 h2
    obtain ⟨hE, hv⟩ := away hQ hu
    rw [vw_mul w _ _ hE (key (1 - s) hs' (by omega)).2.1, hv, zero_add]

end GlobalTheory.Square.Ratio
