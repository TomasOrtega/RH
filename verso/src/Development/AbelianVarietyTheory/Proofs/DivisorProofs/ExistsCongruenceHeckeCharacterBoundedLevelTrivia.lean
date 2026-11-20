import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.HeckeCont

open Formalism.L2.Host GlobalTheory.Mem.Col2.SplitChar

/- English proof (translation)
Break down `eq_or_ne γ 0 with rfl | h0` into its components or cases. Conclude with `zero_le'`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Introduce `D χ S k hS hv`. Use `⟨(∏ q ∈ S, q) ^ k, pow_pos (Finset.prod_pos fun q hq => (hS q hq).pos) k, ?_⟩` and prove the remaining obligations. Introduce and unpack `u hu ⟨s, hs, e⟩`. Use `GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) (fun v x hx => ?_)` and prove the remaining obligations. Rewrite using `[finIdl_fst]`.

Both sides reduce to the same expression. Establish `hU : Valued.v ((finIdl D u : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1` using `finIdl_unit hu v`. Establish `hxU : IsUnitAt v x` using `by show Valued.v (x : v.adicCompletion D.host.E) = 1`. Rewrite using `[hx]`. Conclude with `hU`.

Break down `hv v with hunr | ⟨q, hq, hov, hlev⟩` into its components or cases. Conclude with `hunr x hxU`. Use `hlev x hxU ?_` and prove the remaining obligations. Rewrite using `[hx, vl_sub_one, e]`. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun q : ℕ => q) hq`.

Establish `hP : OverP D.host (∏ q ∈ S, q) v` using `by show (((∏ q ∈ S, q : ℕ)) : 𝓞 D.host.E) ∈ v.asIdeal`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hov`. Establish `h1` using `le_exp_neg_one_of_lt_one (val_nat_lt hP)`. Rewrite using `[map_mul, Nat.cast_pow, map_pow]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_one_of_cong : ∀ (D : D7) (χ : HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hv
  refine ⟨(∏ q ∈ S, q) ^ k, pow_pos (Finset.prod_pos fun q hq => (hS q hq).pos) k, ?_⟩
  rintro u hu ⟨s, hs, e⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu) (fun w => ?_) (fun v x hx => ?_)
  · rw [finIdl_fst]
    rfl
  · have hU : Valued.v ((finIdl D u : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1 := finIdl_unit hu v
    have hxU : IsUnitAt v x := by
      show Valued.v (x : v.adicCompletion D.host.E) = 1
      rw [hx]
      exact hU
    rcases hv v with hunr | ⟨q, hq, hov, hlev⟩
    · exact hunr x hxU
    · refine hlev x hxU ?_
      rw [hx, vl_sub_one, e]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
      have hP : OverP D.host (∏ q ∈ S, q) v := by
        show (((∏ q ∈ S, q : ℕ)) : 𝓞 D.host.E) ∈ v.asIdeal
        rw [hc, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hov
      have h1 := le_exp_neg_one_of_lt_one (val_nat_lt hP)
      rw [map_mul, Nat.cast_pow, map_pow]
      calc vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k * vl D v s ≤ vl D v ((∏ q ∈ S, q : ℕ) : AE D) ^ k :=
            mul_le_of_le_one_right' (vl_le hs v)
        _ ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' h1 k
        _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.HeckeCont
