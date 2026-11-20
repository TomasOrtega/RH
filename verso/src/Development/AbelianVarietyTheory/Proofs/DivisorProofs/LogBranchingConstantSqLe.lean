import Mathlib
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq

open Formalism.BasicNotions

namespace GlobalTheory.BranchBound

/- English proof (translation)
Set `g : ℕ → ℤ` to `fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0`. Establish `h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1))`. Unfold `Formalism.MainNotions.PrimeDegreeVariant.D1`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `a : g i = lam.w ⟨i.1, by omega⟩` using `by simp [g, show i.1 < n + 1 by omega]`.

Establish `b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩` using `by simp [g, show i.1 + 1 < n + 1 by omega]`. Rewrite using `[a, b]`. Conclude with `min_le_left _ _`. Establish `h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]`.

Conclude with `Finset.sum_range_sub' g n`. Establish `a0 : g 0 = lam.w 0` using `by simp [g]`. Establish `an : g n = lam.w (Fin.last n)` using `by simp [g]; rfl`. Rewrite `h1` using `[h2, a0, an]`. Conclude with `h1`.
-/
theorem branching_D1_le_weight_difference (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ lam.w 0 - lam.w (Fin.last n) := by
  let g : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0
  have h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1)) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.D1
    refine Finset.sum_le_sum fun i _ => ?_
    have a : g i = lam.w ⟨i.1, by omega⟩ := by simp [g, show i.1 < n + 1 by omega]
    have b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩ := by simp [g, show i.1 + 1 < n + 1 by omega]
    rw [a, b]
    exact min_le_left _ _
  have h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]
    exact Finset.sum_range_sub' g n
  have a0 : g 0 = lam.w 0 := by simp [g]
  have an : g n = lam.w (Fin.last n) := by simp [g]; rfl
  rw [h2, a0, an] at h1
  exact h1

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

/- English proof (translation)
Establish `hq` using `GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam`. Rewrite `hq` using `[GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi]`. Establish `hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))`. Use `congrArg (Rat.cast : ℚ → ℝ) hq` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Rewrite using `[hr]`. Establish `h6 : (1 : ℝ) ≤ 6 * B` using `by linarith`. Establish `hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, 0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B`. Introduce `i j hj`.

Establish `hij : i < j` using `Finset.mem_Ioi.mp hj`. Establish `hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ)` using `by exact_mod_cast hij`. Establish `hanti : (lam.w j : ℝ) ≤ lam.w i` using `by exact_mod_cast lam.anti hij.le`. Establish `hbi` using `abs_le.mp (hw i)`. Establish `hbj` using `abs_le.mp (hw j)`.

Establish `hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)` using `by linarith`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `apply div_nonneg <;> linarith`. Rewrite using `[div_le_iff₀ hk]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Apply `pow_le_pow_right₀ h6` to reduce the goal to its premises. Simplify using `using Finset.card_le_univ (Finset.Ioi i)`.

Use `_ = (6 * B) ^ (N * N) := by`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]`.
-/
theorem finrank_delSq_le (N : ℕ) (lam : DomWeight N) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) :
    (Module.finrank ℂ (delSq ℂ N lam) : ℝ) ≤ (6 * B) ^ (N * N) := by
  have hq := GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam
  rw [GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi] at hq
  have hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  rw [hr]
  have h6 : (1 : ℝ) ≤ 6 * B := by linarith
  have hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i,
      0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧
      ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hanti : (lam.w j : ℝ) ≤ lam.w i := by exact_mod_cast lam.anti hij.le
    have hbi := abs_le.mp (hw i)
    have hbj := abs_le.mp (hw j)
    have hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_iff₀ hk]
      nlinarith
  calc ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ _i : Fin N, (6 * B) ^ N := by
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_
          calc _ ≤ ∏ _j ∈ Finset.Ioi i, (6 * B) :=
                Finset.prod_le_prod (fun j hj => (hf i j hj).1) fun j hj => (hf i j hj).2
            _ = (6 * B) ^ (Finset.Ioi i).card := Finset.prod_const _
            _ ≤ (6 * B) ^ N := by
                apply pow_le_pow_right₀ h6
                simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = (6 * B) ^ (N * N) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

/- English proof (translation)
Introduce `n N h lam sg B hB hN hw`. Substitute `h` using the available equality. Establish `hNB : ((n + 1 : ℕ) : ℝ) ≤ B` using `hN`. Establish `hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)` using `by positivity`. Establish `hL : 0 < Real.log (6 * B)` using `Real.log_pos (by linarith)`.

Establish `hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B)` using `by positivity`. Establish `hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ)`. Unfold `DomWeight.spread`. Rewrite using `[dif_pos (Nat.succ_pos n)]`. Both sides reduce to the same expression.

Establish `h0` using `abs_le.mp (hw 0)`. Establish `hl` using `abs_le.mp (hw (Fin.last n))`. Establish `hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0` using `by exact_mod_cast lam.anti (Fin.zero_le _)`. Use `set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs`. Establish `hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ))`.

Rewrite using `[hs, hsp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hs2 : 2 ≤ s` using `by rw [hsR]; push_cast at hNB ⊢; linarith`. Establish `hs6 : s ≤ 6 * B` using `by rw [hsR]; push_cast at hNB ⊢; linarith`.

Establish `hls0 : 0 ≤ Real.log s` using `Real.log_nonneg (by linarith)`. Establish `hls : Real.log s ≤ Real.log (6 * B)` using `Real.log_le_log (by linarith) hs6`. Establish `hD` using `branching_D1_le_weight_difference n lam sg`. Establish `hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B`. Establish `: ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n)` using `by exact_mod_cast hD`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he`. Establish `heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ)` using `by rw [he]; push_cast; ring`. Establish `hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B)`. Break down `le_or_gt e 0 with he0 | he0` into its components or cases.

Establish `: e * Real.log s ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg he0 hls0`. Establish `: 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B`. Rewrite using `[heR]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Establish `hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e` using `rfl`. Establish `hcpos : 0 < s ^ e` using `Real.rpow_pos_of_pos (by linarith) e`. Use `set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd`.

Establish `hd0 : 0 ≤ d` using `by positivity`. Establish `hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d`. Unfold `Formalism.MainNotions.PrimeDegreeVariant.brBd`. Rewrite using `[hc, mul_pow, Real.sq_sqrt hd0]`. Rewrite using `[hb2]`.

Break down `eq_or_lt_of_le hd0 with hd0' | hdpos` into its components or cases. Rewrite using `[← hd0', mul_zero, Real.log_zero]`. Conclude with `hR`. Establish `hdle` using `finrank_delSq_le (n + 1) lam B hB hw`. Establish `hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B)`.

Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_le_log hdpos hdle`. Establish `hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B)`. Use `hlogd.trans ?_` and prove the remaining obligations. Use `push_cast`.

Establish `: (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B`. Move the coercions through the operations in `at hNB hN0`. Conclude with `mul_le_mul_of_nonneg_left hNB hN0`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]`.

Move the coercions through the operations in `at hel hlogd' ⊢`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_brBd_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B →
    (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) →
    Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  intro n N h lam sg B hB hN hw
  subst h
  have hNB : ((n + 1 : ℕ) : ℝ) ≤ B := hN
  have hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (6 * B) := Real.log_pos (by linarith)
  have hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity

  have hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ) := by
    unfold DomWeight.spread
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  have h0 := abs_le.mp (hw 0)
  have hl := abs_le.mp (hw (Fin.last n))
  have hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0 := by exact_mod_cast lam.anti (Fin.zero_le _)
  set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs
  have hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ)) := by
    rw [hs, hsp]; push_cast; ring
  have hs2 : 2 ≤ s := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hs6 : s ≤ 6 * B := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ Real.log (6 * B) := Real.log_le_log (by linarith) hs6

  have hD := branching_D1_le_weight_difference n lam sg
  have hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B := by
    have : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n) := by exact_mod_cast hD
    linarith
  set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he
  have heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) := by rw [he]; push_cast; ring
  have hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    rcases le_or_gt e 0 with he0 | he0
    · have : e * Real.log s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hls0
      have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity
      linarith
    · have he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B := by
        rw [heR]; nlinarith
      calc e * Real.log s ≤ (2 * ((n + 1 : ℕ) : ℝ) * B) * Real.log (6 * B) :=
            mul_le_mul he2 hls hls0 (by positivity)
        _ = _ := by ring

  have hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e := rfl
  have hcpos : 0 < s ^ e := Real.rpow_pos_of_pos (by linarith) e
  set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  have hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
    rw [hc, mul_pow, Real.sq_sqrt hd0]
  rw [hb2]
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · rw [← hd0', mul_zero, Real.log_zero]; exact hR
  have hdle := finrank_delSq_le (n + 1) lam B hB hw
  have hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hdpos hdle
  have hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    refine hlogd.trans ?_
    push_cast
    have : (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B := by
      push_cast at hNB hN0
      exact mul_le_mul_of_nonneg_left hNB hN0
    nlinarith
  rw [Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]
  push_cast at hel hlogd' ⊢
  nlinarith

end GlobalTheory.BranchBound
