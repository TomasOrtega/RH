import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

namespace GlobalTheory.PMonE

open Finset in

/- English proof (translation)
Introduce `F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose`. Establish `hp : 1 < p` using `(Fact.out : p.Prime).one_lt`. Establish `hpR : (0 : ℝ) < p` using `by exact_mod_cast (by omega : 0 < p)`. Establish `hl : ∀ j, 0 < ‖lam j‖` using `fun j => norm_pos_iff.mpr (hlam j)`. Establish `hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ` using `fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)`.

Use `choose ρ hρ using hρ`. Establish `hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖` using `fun j => by`. Rewrite using `[← norm_pow, hρ, norm_div]`. Establish `hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖` using `fun j => by`. Rewrite using `[← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn, one_le_div (hl _)]`.

Conclude with `hanti (Fin.castSucc_le_succ j)`. Use `set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'`. Establish `hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖` using `fun n => by`. Simplify using `only [hρ']`. Use `split_ifs with h`.

Conclude with `hρ1 _`. Simplify using the standard rewrite rules. Establish `hρ'ne : ∀ n, ρ' n ≠ 0` using `fun n h0 => by`. Use `hρ'1 n` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP`. Establish `hPne : ∀ j, P j ≠ 0` using `fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n`. Establish `hPsucc : ∀ j, P (j + 1) = P j * ρ' j` using `fun j => prod_range_succ _ _`. Establish `hPmono : Monotone fun j => ‖P j‖`.

Use `monotone_nat_of_le_succ fun j => ?_` and prove the remaining obligations. Simplify using `only [hPsucc, norm_mul]`. Conclude with `le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)`. Establish `hP0 : P 0 = 1` using `by simp [hP]`. Establish `hc1 : 1 ≤ ‖P k‖`.

Use `hPmono (Nat.zero_le k)` as an intermediate fact. Simplify `this` using `[hP0]`. Use `set c := ‖P k‖ with hc`. Establish `hcpos : 0 < c` using `by linarith`. Use `set N := p ^ (k + 1) - 1 with hN`.

Establish `hpk : 2 ≤ p ^ (k + 1)` using `le_trans (by omega) (Nat.le_self_pow (by omega) p)`. Establish `hNpos : 0 < N` using `by omega`. Establish `hN1 : p ^ (k + 1) = N + 1` using `by omega`. Use `set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw`. Establish `hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1))`.

Rewrite using `[hw]`. Simplify using `only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hwne : w ≠ 0`. Rewrite using `[hw]`.

Conclude with `div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by`. Introduce `h0`. Rewrite `hϖ` using `[h0, norm_zero]`. Conclude with `(inv_pos.mpr hpR).ne' hϖ.symm)))`. Use the proof step `(mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))`.

Take `⟨π0, hπ0⟩` from `IsAlgClosed.exists_pow_nat_eq w hNpos`. Establish `hπ0ne : π0 ≠ 0`. Introduce `h0`. Rewrite `hπ0` using `[h0, zero_pow hNpos.ne']`. Conclude with `hwne hπ0.symm`.

Use `set s := ‖π0‖ with hs`. Establish `hspos : 0 < s` using `norm_pos_iff.mpr hπ0ne`. Establish `hsN : s ^ N = ‖w‖` using `by rw [hs, ← norm_pow, hπ0]`. Establish `hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖`. Rewrite using `[div_lt_iff₀ hpR, mul_comm]`.

Conclude with `hclose 0 (Fin.last k)`. Establish `hsc : s * c < 1`. Establish `key : (s * c) ^ N < 1`. Establish `hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c)`. Rewrite using `[hwn, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key`. Use `⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_mul, ← hs]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]`. Establish `: ρ' j = ρ j` using `by simp [hρ', j.isLt]`. Rewrite using `[this, hρn]`.

Use `hl j.succ` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Simplify using `only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]`. Rewrite using `[← pow_succ, hN1, pow_succ s N, hsN, hwn]`. Use `hl (Fin.last k)` as an intermediate fact.

Clear the denominators using the available nonvanishing facts.
-/
theorem _root_.GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp

end GlobalTheory.PMonE
