import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHHyperA

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/- English proof (translation)
Establish `e : Icc 1 m = Ioc 0 m` using `by ext x; simp; omega`. Use `Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem charSum_le (hχ : χ ≠ 1) (m : ℕ) : ‖∑ n ∈ Ioc 0 m, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have e : Icc 1 m = Ioc 0 m := by ext x; simp; omega
  have := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ m
  rwa [e] at this

/- English proof (translation)
Establish `h` using `Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ) 1 (by simp) N hN`. Establish `e : Icc 1 N = Ioc 0 N` using `by ext x; simp; omega`. Establish `e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N`. Rewrite using `[e, cS]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.cpow_neg_one, div_eq_mul_inv]`. Rewrite `h` using `[e2]`. Establish `e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹` using `by simp [Real.rpow_neg_one]`. Rewrite `h` using `[e3]`. Simplify using `only [norm_one, Complex.one_re, div_one] at h`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem cS_approx (hχ : χ ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖DirichletCharacter.LFunction χ 1 - cS χ N‖ ≤ 4 * ((q : ℝ) + 1) / N := by
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1) (Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ)
    1 (by simp) N hN
  have e : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  have e2 : ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-(1 : ℂ)) = cS χ N := by
    rw [e, cS]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.cpow_neg_one, div_eq_mul_inv]
  rw [e2] at h
  have e3 : (N : ℝ) ^ (-(1 : ℂ).re) = (N : ℝ)⁻¹ := by simp [Real.rpow_neg_one]
  rw [e3] at h
  simp only [norm_one, Complex.one_re, div_one] at h
  calc _ ≤ 2 * ((q : ℝ) + 1) * (1 + 1) * (N : ℝ)⁻¹ := h
    _ = 4 * ((q : ℝ) + 1) / N := by ring

/- English proof (translation)
Introduce `V hV`. Proceed by induction on `V, hV using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ V hUV ih`. Rewrite using `[Finset.sum_Ioc_succ_top hUV, ih, Finset.sum_Ioc_succ_top hUV, Finset.sum_Ioc_succ_top (Nat.zero_le V)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abel_identity (c : ℕ → ℂ) (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, c n * (w n : ℂ) =
      (∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ) +
        ∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih =>
    rw [Finset.sum_Ioc_succ_top hUV, ih, Finset.sum_Ioc_succ_top hUV,
      Finset.sum_Ioc_succ_top (Nat.zero_le V)]
    push_cast
    ring

/- English proof (translation)
Introduce `V hV`. Proceed by induction on `V, hV using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tele (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, (w n - w (n + 1)) = w (U + 1) - w (V + 1) := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hUV ih => rw [Finset.sum_Ioc_succ_top hUV, ih]; ring

/- English proof (translation)
Rewrite using `[abel_identity c w U V hUV]`. Establish `hV : 0 ≤ w (V + 1)`. Break down `hUV.lt_or_eq with h | h` into its components or cases. Conclude with `(hw V h).1`. Rewrite using `[← h]`.

Conclude with `hw0`. Establish `h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1)`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]`. Conclude with `mul_le_mul_of_nonneg_right (hA V) hV`. Establish `h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1)`.

Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]`. Conclude with `mul_le_mul_of_nonneg_right (hA U) hw0`. Establish `h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤ B * (w (U + 1) - w (V + 1))`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun n hn => ?_` and prove the remaining obligations.

Establish `hn' : U < n` using `(Finset.mem_Ioc.mp hn).1`. Establish `hd : 0 ≤ w n - w (n + 1)` using `by linarith [(hw n hn').2]`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]`. Conclude with `mul_le_mul_of_nonneg_right (hA n) hd`. Use `_ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]`.

Establish `h4` using `norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)) (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))`. Establish `h5` using `norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abel_bound (c : ℕ → ℂ) (w : ℕ → ℝ) (B : ℝ) (hA : ∀ m, ‖∑ n ∈ Ioc 0 m, c n‖ ≤ B)
    (U V : ℕ) (hUV : U ≤ V) (hw0 : 0 ≤ w (U + 1))
    (hw : ∀ n, U < n → 0 ≤ w (n + 1) ∧ w (n + 1) ≤ w n) :
    ‖∑ n ∈ Ioc U V, c n * (w n : ℂ)‖ ≤ 2 * B * w (U + 1) := by
  rw [abel_identity c w U V hUV]
  have hV : 0 ≤ w (V + 1) := by
    rcases hUV.lt_or_eq with h | h
    · exact (hw V h).1
    · rw [← h]; exact hw0
  have h1 : ‖(∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)‖ ≤ B * w (V + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hV]
    exact mul_le_mul_of_nonneg_right (hA V) hV
  have h2 : ‖(∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ)‖ ≤ B * w (U + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hA U) hw0
  have h3 : ‖∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
      B * (w (U + 1) - w (V + 1)) := by
    calc _ ≤ ∑ n ∈ Ioc U V, ‖(∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc U V, B * (w n - w (n + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' : U < n := (Finset.mem_Ioc.mp hn).1
        have hd : 0 ≤ w n - w (n + 1) := by linarith [(hw n hn').2]
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hA n) hd
      _ = B * (w (U + 1) - w (V + 1)) := by rw [← Finset.mul_sum, tele w U V hUV]
  have h4 := norm_add_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
    (∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ))
  have h5 := norm_sub_le ((∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ)) ((∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ))
  linarith

def lw (n : ℕ) : ℝ := Real.log n / n

/- English proof (translation)
The claim follows from `div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)`.
-/
theorem lw_nonneg (n : ℕ) : 0 ≤ lw n :=
  div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)

/- English proof (translation)
Use `⟨lw_nonneg _, ?_⟩` and prove the remaining obligations. Establish `h3 : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `he : Real.exp 1 ≤ (n : ℝ)`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `lw`. Use `push_cast`. Conclude with `Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)`.
-/
theorem lw_anti (n : ℕ) (hn : 3 ≤ n) : 0 ≤ lw (n + 1) ∧ lw (n + 1) ≤ lw n := by
  refine ⟨lw_nonneg _, ?_⟩
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp 1 ≤ (n : ℝ) := by
    have := Real.exp_one_lt_d9; linarith
  unfold lw
  push_cast
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (by linarith)) (by linarith)

/- English proof (translation)
Rewrite using `[cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Unfold `lw`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cT_sub (U V : ℕ) (hUV : U ≤ V) :
    cT χ V - cT χ U = ∑ n ∈ Ioc U V, χ (n : ZMod q) * (lw n : ℂ) := by
  rw [cT, cT, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUV, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold lw; push_cast; ring

/- English proof (translation)
Rewrite using `[cT_sub χ U V hUV]`. Conclude with `abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _) (fun n hn => lw_anti n (by omega))`.
-/
theorem cT_diff2 (hχ : χ ≠ 1) (U V : ℕ) (hU : 2 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 2 * ((q : ℝ) + 1) * lw (U + 1) := by
  rw [cT_sub χ U V hUV]
  exact abel_bound (fun n => χ (n : ZMod q)) lw _ (charSum_le χ hχ) U V hUV (lw_nonneg _)
    (fun n hn => lw_anti n (by omega))

/- English proof (translation)
Establish `hq : (0 : ℝ) ≤ q` using `Nat.cast_nonneg q`. Establish `hU0 : (1 : ℝ) ≤ U` using `by exact_mod_cast hU`. Establish `hlU : 0 ≤ Real.log ((U : ℝ) + 1)` using `Real.log_nonneg (by linarith)`. Break down `(show 2 ≤ U ∨ U = 1 by omega) with h2 | h1` into its components or cases. Establish `h` using `cT_diff2 χ hχ U V h2 hUV`.

Establish `e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1)` using `by unfold lw; push_cast; rfl`. Rewrite `h` using `[e]`. Establish `: Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)` using `div_le_div_of_nonneg_right (by linarith) (by linarith)`. Establish `hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Substitute `h1` using the available equality. Break down `(show V = 1 ∨ 2 ≤ V by omega) with hv | hv` into its components or cases. Substitute `hv` using the available equality. Simplify using `only [sub_self, norm_zero]`. Check the signs of the components of the expression.

Establish `hA` using `cT_diff2 χ hχ 2 V le_rfl hv`. Establish `hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2`. Rewrite using `[cT_sub χ 1 2 (by norm_num)]`. Establish `e : Ioc 1 2 = {2}` using `by decide`. Rewrite using `[e, Finset.sum_singleton]`.

Rewrite using `[norm_mul, Complex.norm_real]`. Establish `hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1` using `DirichletCharacter.norm_le_one χ _`. Establish `hl : ‖lw 2‖ ≤ 1 / 2`. Rewrite using `[Real.norm_of_nonneg (lw_nonneg 2)]`. Unfold `lw`.

Use `push_cast`. Use `Real.log_two_lt_d9` as an intermediate fact. Rewrite using `[div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hl3 : lw 3 ≤ 2 / 3`.

Unfold `lw`. Use `push_cast`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)` as an intermediate fact. Rewrite using `[div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith`. Establish `hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1)` using `by ring`.

Rewrite using `[hsplit]`. Establish `hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ))` using `Real.log_nonneg (by norm_num)`. Establish `: (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2` using `by push_cast; push_cast at hl2`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `: 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3)` using `mul_le_mul_of_nonneg_left hl3 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ _ := by nlinarith`.
-/
theorem cT_diff (hχ : χ ≠ 1) (U V : ℕ) (hU : 1 ≤ U) (hUV : U ≤ V) :
    ‖cT χ V - cT χ U‖ ≤ 4 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hU0 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hlU : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by linarith)
  rcases (show 2 ≤ U ∨ U = 1 by omega) with h2 | h1
  · have h := cT_diff2 χ hχ U V h2 hUV
    have e : lw (U + 1) = Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) := by unfold lw; push_cast; rfl
    rw [e] at h
    have : Real.log ((U : ℝ) + 1) / ((U : ℝ) + 1) ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hy : 0 ≤ (1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1) := by positivity
    calc _ ≤ _ := h
      _ ≤ 2 * ((q : ℝ) + 1) * ((1 + Real.log ((U : ℝ) + 1)) / ((U : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by nlinarith
  · subst h1
    rcases (show V = 1 ∨ 2 ≤ V by omega) with hv | hv
    · subst hv; simp only [sub_self, norm_zero]; positivity
    · have hA := cT_diff2 χ hχ 2 V le_rfl hv
      have hB : ‖cT χ 2 - cT χ 1‖ ≤ 1 / 2 := by
        rw [cT_sub χ 1 2 (by norm_num)]
        have e : Ioc 1 2 = {2} := by decide
        rw [e, Finset.sum_singleton]
        rw [norm_mul, Complex.norm_real]
        have hc : ‖χ ((2 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hl : ‖lw 2‖ ≤ 1 / 2 := by
          rw [Real.norm_of_nonneg (lw_nonneg 2)]
          unfold lw; push_cast
          have := Real.log_two_lt_d9
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
        calc _ ≤ 1 * (1 / 2 : ℝ) := mul_le_mul hc hl (norm_nonneg _) (by norm_num)
          _ = 1 / 2 := by ring
      have hl3 : lw 3 ≤ 2 / 3 := by
        unfold lw; push_cast
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
      have hsplit : cT χ V - cT χ 1 = (cT χ V - cT χ 2) + (cT χ 2 - cT χ 1) := by ring
      rw [hsplit]
      have hl2 : 0 ≤ Real.log ((1 : ℕ) + (1 : ℝ)) := Real.log_nonneg (by norm_num)
      have : (1 : ℝ) ≤ (1 + Real.log ((1 : ℕ) + (1 : ℝ))) / ((1 : ℕ) + (1 : ℝ)) * 2 := by
        push_cast; push_cast at hl2
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; linarith
      calc _ ≤ ‖cT χ V - cT χ 2‖ + ‖cT χ 2 - cT χ 1‖ := norm_add_le _ _
        _ ≤ 2 * ((q : ℝ) + 1) * (2 / 3) + 1 / 2 := by
          have : 2 * ((q : ℝ) + 1) * lw (2 + 1) ≤ 2 * ((q : ℝ) + 1) * (2 / 3) :=
            mul_le_mul_of_nonneg_left hl3 (by positivity)
          linarith
        _ ≤ _ := by nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
