import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

/- English proof (translation)
Establish `hk : 1 ≤ R.k` using `by have := R.m_add_three_le_k; omega`. Establish `hm : (0 : ℝ) < R.m`. Use `R.two_le_m` as an intermediate fact. Conclude with `(by omega : 0 < R.m)` after adjusting the coercions. Establish `hmf : (R.m : ℝ) ≤ R.f`.

Establish `: R.m ≤ R.f` using `R.m_le_f`. Conclude with `this` after adjusting the coercions. Establish `hL : 1 ≤ s.L` using `Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le`. Establish `hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1`. Establish `: (1 : ℝ) ≤ R.k` using `by exact_mod_cast hk`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL2 : 1 ≤ s.L ^ 2` using `one_le_pow₀ hL`. Establish `h1 : (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m`. Rewrite using `[le_div_iff₀ hm]`. Establish `hA : (0 : ℝ) ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3` using `by positivity`.

Establish `hf : (0 : ℝ) ≤ R.f` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `Nat.le_ceil (10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8)`. Establish `h3 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m)` using `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Establish `h4 : ((10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) : ℕ) : ℝ) ≤ (nWv R s : ℕ)`.

Unfold `nWv`. Move the coercions through the operations in `[Nat.cast_sub hk]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h4` after adjusting the coercions.
-/
theorem nWv_lower (R : Ranks) (s : Scale) :
    10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) ≤ nWv R s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hm : (0 : ℝ) < R.m := by
    have := R.two_le_m
    exact_mod_cast (by omega : 0 < R.m)
  have hmf : (R.m : ℝ) ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    exact_mod_cast this
  have hL : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le
  have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
    linarith
  have hL2 : 1 ≤ s.L ^ 2 := one_le_pow₀ hL
  have h1 : (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 ≤
      (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    rw [le_div_iff₀ hm]
    have hA : (0 : ℝ) ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 := by positivity
    have hf : (0 : ℝ) ≤ R.f := by positivity
    calc (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.m ≤ (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3 * R.f :=
          mul_le_mul_of_nonneg_left hmf hA
      _ = (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (by positivity)
  have h2 := Nat.le_ceil (10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8)
  have h3 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) * ((R.k : ℝ) - 1) ^ 3) ≤
      10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : ((10 * R.r * (R.f + R.f * (R.k - 1) ^ 3) : ℕ) : ℝ) ≤ (nWv R s : ℕ) := by
    unfold nWv
    push_cast [Nat.cast_sub hk]
    linarith
  exact_mod_cast h4

/- English proof (translation)
Establish `h` using `nWv_lower R s`. Establish `h2` using `R.two_le_m`. Establish `h3` using `R.m_add_three_le_k`. Establish `hf : 2 ≤ R.f` using `le_trans h2 R.m_le_f`. Establish `hr : R.r = R.k + R.m - 1` using `rfl`.

Generalize the expression as in `nWv R s = W at h`. Generalize the expression as in `R.f = f at *`. Generalize the expression as in `R.r = r at *`. Take `⟨j, hj⟩ : ∃ j, R.k - 1 = j` from `⟨_, rfl⟩`. Rewrite `h`, the goal using `[hj]`.

Establish `hj1 : 1 ≤ j` using `by omega`. Establish `hjr : j ≤ r` using `by omega`. Establish `hrj : r + 1 ≤ 2 * j` using `by omega`. Establish `hj3 : j ≤ j ^ 3` using `Nat.le_self_pow (by norm_num) j`. Establish `hfr : 2 * 2 ≤ f * r` using `Nat.mul_le_mul hf (by omega)`.

Establish `e : 10 * r * (f + f * j ^ 3) = 10 * (f * r) + f * r * (10 * j ^ 3)` using `by ring`. Rewrite `h` using `[e]`. Establish `a1 : f * r * (r + 1) ≤ f * r * (10 * j ^ 3)` using `Nat.mul_le_mul_left _ (by omega)`. Establish `a2 : j * f ≤ f * r` using `by rw [mul_comm]; exact Nat.mul_le_mul_left _ hjr`. Establish `a3 : 2 * r ≤ f * r` using `Nat.mul_le_mul_right _ hf`.

Establish `a4 : 8 * f * r = 8 * (f * r)` using `by ring`. Use `⟨by omega, by omega, by omega⟩` and prove the remaining obligations.
-/
theorem nWv_three_lower (R : Ranks) (s : Scale) :
    R.f * R.r * (R.r + 1) ≤ nWv R s ∧ (R.k - 1) * R.f + 2 * R.r ≤ nWv R s ∧
      8 * R.f * R.r + 4 ≤ nWv R s := by
  have h := nWv_lower R s
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hf : 2 ≤ R.f := le_trans h2 R.m_le_f
  have hr : R.r = R.k + R.m - 1 := rfl
  generalize nWv R s = W at h
  generalize R.f = f at *
  generalize R.r = r at *
  obtain ⟨j, hj⟩ : ∃ j, R.k - 1 = j := ⟨_, rfl⟩
  rw [hj] at h ⊢
  have hj1 : 1 ≤ j := by omega
  have hjr : j ≤ r := by omega
  have hrj : r + 1 ≤ 2 * j := by omega
  have hj3 : j ≤ j ^ 3 := Nat.le_self_pow (by norm_num) j
  have hfr : 2 * 2 ≤ f * r := Nat.mul_le_mul hf (by omega)
  have e : 10 * r * (f + f * j ^ 3) = 10 * (f * r) + f * r * (10 * j ^ 3) := by ring
  rw [e] at h
  have a1 : f * r * (r + 1) ≤ f * r * (10 * j ^ 3) := Nat.mul_le_mul_left _ (by omega)
  have a2 : j * f ≤ f * r := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hjr
  have a3 : 2 * r ≤ f * r := Nat.mul_le_mul_right _ hf
  have a4 : 8 * f * r = 8 * (f * r) := by ring
  refine ⟨by omega, by omega, by omega⟩

/- English proof (translation)
Introduce `eps _ _ C hC`. Use `⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩` and prove the remaining obligations. Establish `hW : C.P.CnW = 10`. Establish `hF` using `hC.1`. Unfold `FC.Fixed at hF`.

The claim follows by propositional logic. Establish `hT : C.T.cTO = 377` using `hC.2.2.2.2.2.2.2.2.2.1`. Establish `hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `: (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast this`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨⟨?_, ?_⟩, Dvd.intro _ rfl, hV.ranks.2.2.2, ?_, ?_, by omega, by omega, nWv_three_lower _ _⟩` and prove the remaining obligations. Rewrite using `[hW]`. Unfold `nW nWv`. Use `Nat.le_ceil (10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8)` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hW]`. Unfold `nW nWv`. Use `Nat.ceil_lt_add_one (a := 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8) (by positivity)` as an intermediate fact.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hT]`. Both sides reduce to the same expression. Take `⟨a, ha⟩` from `D.R.k_even`.

Take `⟨b, hb⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Conclude with `⟨a + b + 2, by omega⟩`.
-/
theorem szRow_nW : SzRow (fun C D L => (nW L C.P.CnW ≤ ((nWv D.R L.sc : ℕ) : ℝ) ∧ ((nWv D.R L.sc : ℕ) : ℝ) < nW L C.P.CnW + 8) ∧ (8 ∣ (nWv D.R L.sc : ℕ)) ∧ (D.R.r + D.R.t = (8 * D.R.f * D.R.r + 4 : ℕ) + (TOv L.sc : ℕ) * (nWv D.R L.sc : ℕ)) ∧ ((TOv L.sc : ℕ) = ⌈L.sc.x ^ C.T.cTO⌉₊) ∧ (Odd (D.R.r + 6 : ℕ)) ∧ (D.R.r + 5 < (D.R.r + 6 : ℕ)) ∧ ((D.R.r + 6 : ℕ) ≤ D.R.r + 7) ∧ (D.R.f * D.R.r * (D.R.r + 1) ≤ (nWv D.R L.sc : ℕ) ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ (nWv D.R L.sc : ℕ) ∧ (8 * D.R.f * D.R.r + 4 : ℕ) ≤ (nWv D.R L.sc : ℕ))) := by
  intro eps _ _ C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun D L _ _ hV => ?_⟩⟩⟩
  have hW : C.P.CnW = 10 := by
    have hF := hC.1
    unfold FC.Fixed at hF
    tauto
  have hT : C.T.cTO = 377 := hC.2.2.2.2.2.2.2.2.2.1
  have hk : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    have : (1 : ℝ) ≤ D.R.k := by exact_mod_cast this
    linarith
  refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl, hV.ranks.2.2.2, ?_, ?_, by omega, by omega, nWv_three_lower _ _⟩
  · rw [hW]; unfold nW nWv
    have := Nat.le_ceil (10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8)
    push_cast
    linarith
  · rw [hW]; unfold nW nWv
    have := Nat.ceil_lt_add_one (a := 10 * (D.R.r : ℝ) * ((D.R.f : ℝ) + (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m) / 8) (by positivity)
    push_cast
    linarith
  · rw [hT]; rfl
  · obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have := D.R.two_le_m
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    exact ⟨a + b + 2, by omega⟩

end GlobalTheory.EX
