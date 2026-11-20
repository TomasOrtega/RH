import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertFix

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one`. Consider the case `exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one`. Consider the case `(apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one ..)`.
-/
theorem eq_one_of_pow_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = 1) (u : K) (hu : u ^ m = 1) (h1 : ‖u - 1‖ < 1) : u = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | (apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one ..)

/- English proof (translation)
Introduce `l hl n hn σ hσ x hx`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, map_zero]`. Establish `hlp : 1 < l ^ n` using `Nat.one_lt_pow hn.ne' hl.out.one_lt`. Take `⟨m, hm⟩ : ∃ m, l ^ n = m + 1` from `⟨l ^ n - 1, by omega⟩`.

Establish `hm0 : m ≠ 0` using `by omega`. Establish `hxm : x ^ m = 1`. Rewrite `hx` using `[hm, pow_succ]`. Conclude with `mul_right_cancel₀ hx0 (by rw [hx, one_mul])`. Establish `hnx : ‖x‖ = 1`.

Establish `: ‖x‖ ^ m = 1` using `by rw [← norm_pow, hxm, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this`. Establish `hcop : l.Coprime m`. Establish `h : (l ^ n).Coprime m` using `by rw [hm]; simp`. Conclude with `Nat.Coprime.of_dvd_left (dvd_pow_self l hn.ne') h`.

Establish `hmn : ‖(m : Om l)‖ = 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_natCast_eq_one_iff.2 hcop`. Establish `hu : σ x / x = 1`. Use `eq_one_of_pow_eq_one m hmn _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[div_pow, ← map_pow, hxm, map_one, div_one]`. Establish `e : σ x / x - 1 = (σ x - x) / x` using `by field_simp`. Rewrite using `[e, norm_div, hnx, div_one]`. Conclude with `hσ x hnx.le`. Conclude with `(div_eq_one_iff_eq hx0).1 hu`.
-/
theorem inertia_fix : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ σ : GQ l,
    (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → ∀ x : Om l, x ^ l ^ n = x → σ x = x := by
  intro l hl n hn σ hσ x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hlp : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.out.one_lt
  obtain ⟨m, hm⟩ : ∃ m, l ^ n = m + 1 := ⟨l ^ n - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hxm : x ^ m = 1 := by
    rw [hm, pow_succ] at hx
    exact mul_right_cancel₀ hx0 (by rw [hx, one_mul])
  have hnx : ‖x‖ = 1 := by
    have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this
  have hcop : l.Coprime m := by
    have h : (l ^ n).Coprime m := by rw [hm]; simp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self l hn.ne') h
  have hmn : ‖(m : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 hcop
  have hu : σ x / x = 1 := by
    refine eq_one_of_pow_eq_one m hmn _ ?_ ?_
    · rw [div_pow, ← map_pow, hxm, map_one, div_one]
    · have e : σ x / x - 1 = (σ x - x) / x := by field_simp
      rw [e, norm_div, hnx, div_one]
      exact hσ x hnx.le
  exact (div_eq_one_iff_eq hx0).1 hu

end GlobalTheory.InertFix
