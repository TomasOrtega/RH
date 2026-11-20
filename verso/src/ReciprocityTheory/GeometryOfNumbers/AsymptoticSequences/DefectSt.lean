import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Topology Asymptotics

def hsDefect (D : ℕ) (chi : ℕ → ℝ) (top : ℝ) (n : ℕ) : ℝ :=
  chi n - top * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)

/- English proof (translation)
Establish `ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop` using `tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop`. Establish `h1 : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) + 1` using `Real.isLittleO_log_id_atTop.comp_tendsto ht`. Establish `h2 : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ)`. Use `IsBigO.of_bound 2 ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with n hn`.

Establish `: (1:ℝ) ≤ n` using `by exact_mod_cast hn`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `(isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO (h1.trans_isBigO h2)`. Conclude with `h3.congr (fun n => rfl) (fun n => by ring)`.
-/
theorem isLittleO_pow_mul_log (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto ht
  have h2 : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have h3 := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO (h1.trans_isBigO h2)
  exact h3.congr (fun n => rfl) (fun n => by ring)

/- English proof (translation)
Establish `h1 : (fun _n : ℕ => (j : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ)`. Establish `: (fun _n : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ)`. Rewrite using `[isLittleO_one_left_iff]`. Simplify `(tendsto_natCast_atTop_atTop (R := ℝ)).congr' (Eventually.of_forall fun n => by simp)` using `[Real.norm_eq_abs]`. Simplify using `using this.const_mul_left (j : ℝ)`.

Establish `h2` using `(IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := atTop)).add_isLittleO h1`. Conclude with `h2.pow D`.
-/
theorem isEquivalent_add_pow (D j : ℕ) :
    (fun n : ℕ => ((n : ℝ) + j) ^ D) ~[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun _n : ℕ => (j : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have : (fun _n : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
      rw [isLittleO_one_left_iff]
      simpa [Real.norm_eq_abs] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).congr' (Eventually.of_forall fun n => by simp)
    simpa using this.const_mul_left (j : ℝ)
  have h2 := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := atTop)).add_isLittleO h1
  exact h2.pow D

/- English proof (translation)
Establish `h1` using `(isLittleO_pow_mul_log D).comp_tendsto (tendsto_add_atTop_nat j)`. Establish `h2` using `(isEquivalent_add_pow (D + 1) j).isBigO`. Establish `h3` using `h1.trans_isBigO (h2.congr_left (fun n => by simp))`. Conclude with `h3`.
-/
theorem isLittleO_shift_pow_mul_log (D j : ℕ) :
    (fun n : ℕ => ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h1 := (isLittleO_pow_mul_log D).comp_tendsto (tendsto_add_atTop_nat j)
  have h2 := (isEquivalent_add_pow (D + 1) j).isBigO
  have h3 := h1.trans_isBigO (h2.congr_left (fun n => by simp))
  exact h3

/- English proof (translation)
Establish `h` using `(isEquivalent_add_pow (D + 1) 1).isLittleO`. Conclude with `h.congr (fun n => by simp) (fun n => rfl)`.
-/
theorem isLittleO_succ_pow_sub (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := (isEquivalent_add_pow (D + 1) 1).isLittleO
  exact h.congr (fun n => by simp) (fun n => rfl)

/- English proof (translation)
Establish `hmn : (m : ℝ) ≤ n` using `by exact_mod_cast h`. Establish `hm0 : (0 : ℝ) ≤ m` using `by positivity`. Establish `hl0 : 0 ≤ Real.log ((m : ℝ) + 1)` using `Real.log_nonneg (by linarith)`. Establish `hl : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1)` using `Real.log_le_log (by linarith) (by linarith)`. Conclude with `mul_le_mul (pow_le_pow_left₀ hm0 hmn D) hl hl0 (by positivity)`.
-/
theorem powLog_mono (D : ℕ) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) ^ D * Real.log ((m : ℝ) + 1) ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hl0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul (pow_le_pow_left₀ hm0 hmn D) hl hl0 (by positivity)

/- English proof (translation)
Establish `: (0 : ℝ) ≤ n` using `by positivity`. Conclude with `mul_nonneg (by positivity) (Real.log_nonneg (by linarith))`.
-/
theorem powLog_nonneg (D n : ℕ) : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have : (0 : ℝ) ≤ n := by positivity
  exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1` using `hC (n + k) (by omega)`.

Establish `h2 : C * (((n + k : ℕ) : ℝ) ^ D) * Real.log (((n + k : ℕ) : ℝ) + 1) ≤ |C| * (((n + k : ℕ) : ℝ) ^ D * Real.log (((n + k : ℕ) : ℝ) + 1))`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self C) (powLog_nonneg D (n + k))`. Establish `h3 : chiP D (n + (k + 1)) = chiP D (n + k + 1)` using `by rw [Nat.add_assoc]`. Rewrite using `[h3]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chiP_add_sub_le (D : ℕ) (C : ℝ)
    (hC : ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1))
    (k n : ℕ) (hn : 1 ≤ n) :
    chiP D (n + k) - chiP D n ≤
      ∑ j ∈ Finset.range k, |C| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 := hC (n + k) (by omega)
    have h2 : C * (((n + k : ℕ) : ℝ) ^ D) * Real.log (((n + k : ℕ) : ℝ) + 1) ≤
        |C| * (((n + k : ℕ) : ℝ) ^ D * Real.log (((n + k : ℕ) : ℝ) + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (powLog_nonneg D (n + k))
    have h3 : chiP D (n + (k + 1)) = chiP D (n + k + 1) := by rw [Nat.add_assoc]
    rw [h3]
    linarith

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_chiP_le D`. Use `⟨|C| + |hh|, fun n => ?_⟩` and prove the remaining obligations. Establish `h0` using `chiP_nonneg D n`. Establish `h1` using `hC n`. Establish `hp : (0:ℝ) ≤ (n:ℝ) ^ (D + 1)` using `by positivity`.

Establish `hFpos : (0:ℝ) < ((D + 1).factorial : ℝ)` using `by positivity`. Establish `hf : (1:ℝ) ≤ ((D + 1).factorial : ℝ)`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)` after adjusting the coercions. Establish `hq : |hh * (n:ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)| ≤ |hh| * (n:ℝ) ^ (D + 1)`. Rewrite using `[abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hFpos]`.

Conclude with `div_le_self (by positivity) hf`. Establish `hc : chiP D n ≤ |C| * (n:ℝ) ^ (D + 1)` using `h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)`. Establish `hq'` using `abs_le.mp hq`. Unfold `hsDefect`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> nlinarith [abs_nonneg C, abs_nonneg hh]`.
-/
theorem hilbertSamuelDefect_projectiveSpace_abs_le (D : ℕ) (hh : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |hsDefect D (chiP D) hh n| ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_le D
  refine ⟨|C| + |hh|, fun n => ?_⟩
  have h0 := chiP_nonneg D n
  have h1 := hC n
  have hp : (0:ℝ) ≤ (n:ℝ) ^ (D + 1) := by positivity
  have hFpos : (0:ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hf : (1:ℝ) ≤ ((D + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : |hh * (n:ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)| ≤ |hh| * (n:ℝ) ^ (D + 1) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hFpos]
    exact div_le_self (by positivity) hf
  have hc : chiP D n ≤ |C| * (n:ℝ) ^ (D + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
  have hq' := abs_le.mp hq
  unfold hsDefect
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C, abs_nonneg hh]

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_chiP_succ_sub_le D`. Establish `hA : (fun n : ℕ => chiP D (n + 1) - chiP D n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1)`. Use `IsBigO.trans_isLittleO ?_ (isLittleO_pow_mul_log D)` and prove the remaining obligations. Use `IsBigO.of_bound |C| ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with n hn`.

Establish `h0` using `chiP_succ_sub_nonneg D n`. Establish `h1` using `hC n hn`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, ← abs_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB` using `(isLittleO_succ_pow_sub D).const_mul_left (hh / ((D + 1).factorial : ℝ))`.

Use `(hA.sub hB).congr (fun n => ?_) (fun n => rfl)` and prove the remaining obligations. Simplify using `only [hsDefect]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO (D : ℕ) (hh : ℝ) :
    (fun n => hsDefect D (chiP D) hh (n + 1) - hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_succ_sub_le D
  have hA : (fun n : ℕ => chiP D (n + 1) - chiP D n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_mul_log D)
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 := chiP_succ_sub_nonneg D n
    have h1 := hC n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, ← abs_mul]
    calc chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := h1
      _ = C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ |C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))| := le_abs_self _
  have hB := (isLittleO_succ_pow_sub D).const_mul_left (hh / ((D + 1).factorial : ℝ))
  refine (hA.sub hB).congr (fun n => ?_) (fun n => rfl)
  simp only [hsDefect]
  push_cast
  ring

/- English proof (translation)
Take `⟨C', hC'⟩` from `exists_chiP_succ_sub_le D`. Use `set T : ℕ → ℝ := fun n => ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) with hT_def`. Establish `hT : T =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1)`. Use `IsLittleO.fun_sum (s := Finset.range k) (A := fun j n => |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))) (fun j _ => (isLittleO_shift_pow_mul_log D j).const_mul_left |C'|)` as an intermediate fact. Conclude with `this`.

Establish `hW : (fun n : ℕ => δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1)` using `(hT.const_mul_left δ).add ((isLittleO_pow_mul_log D).const_mul_left |C|)`. Use `IsBigO.trans_isLittleO ?_ hW` and prove the remaining obligations. Use `IsBigO.of_bound 1 ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (k + 1)] with n hn`. Establish `hX0` using `powLog_nonneg D n`.

Establish `hCX : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self C) hX0`. Establish `hCX' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1)`. Rewrite using `[mul_assoc, neg_mul_eq_neg_mul]`.

Conclude with `mul_le_mul_of_nonneg_right (neg_abs_le C) hX0`. Establish `hT0 : 0 ≤ T n` using `Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (powLog_nonneg D (n + j))`. Establish `hup` using `hhi n (by omega)`. Establish `hd1` using `chiP_add_sub_le D C' hC' k n (by omega)`. Establish `hd1'` using `mul_le_mul_of_nonneg_left hd1 hδ`.

Rewrite `hd1'` using `[mul_sub]`. Establish `hlow` using `hlo n hn`. Establish `hm : n - k + k = n` using `by omega`. Establish `hd2` using `chiP_add_sub_le D C' hC' k (n - k) (by omega)`. Rewrite `hd2` using `[hm]`.

Establish `hTm : T (n - k) ≤ T n`. Use `Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)` and prove the remaining obligations. Conclude with `powLog_mono D (by omega)`. Establish `hd2'` using `mul_le_mul_of_nonneg_left (hd2.trans hTm) hδ`. Rewrite `hd2'` using `[mul_sub]`.

Establish `hTn : T n = ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))` using `rfl`. Rewrite `hd1'` using `[← hTn]`. Establish `hW0 : 0 ≤ δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))` using `add_nonneg (mul_nonneg hδ hT0) (mul_nonneg (abs_nonneg _) hX0)`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hW0, one_mul, abs_le]`. Establish `he : hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n = chi n - δ * chiP D n`.

Simplify using `only [hsDefect]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem defect_of_sandwich (D k : ℕ) (δ hh C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  set T : ℕ → ℝ := fun n =>
    ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
    with hT_def
  have hT : T =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    have := IsLittleO.fun_sum (s := Finset.range k)
      (A := fun j n => |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)))
      (fun j _ => (isLittleO_shift_pow_mul_log D j).const_mul_left |C'|)
    exact this
  have hW : (fun n : ℕ => δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    (hT.const_mul_left δ).add ((isLittleO_pow_mul_log D).const_mul_left |C|)
  refine IsBigO.trans_isLittleO ?_ hW
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hX0 := powLog_nonneg D n
  have hCX : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hX0
  have hCX' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, neg_mul_eq_neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_abs_le C) hX0
  have hT0 : 0 ≤ T n := Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (powLog_nonneg D (n + j))

  have hup := hhi n (by omega)
  have hd1 := chiP_add_sub_le D C' hC' k n (by omega)
  have hd1' := mul_le_mul_of_nonneg_left hd1 hδ
  rw [mul_sub] at hd1'

  have hlow := hlo n hn
  have hm : n - k + k = n := by omega
  have hd2 := chiP_add_sub_le D C' hC' k (n - k) (by omega)
  rw [hm] at hd2
  have hTm : T (n - k) ≤ T n := by
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact powLog_mono D (by omega)
  have hd2' := mul_le_mul_of_nonneg_left (hd2.trans hTm) hδ
  rw [mul_sub] at hd2'
  have hTn : T n = ∑ j ∈ Finset.range k,
      |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := rfl
  rw [← hTn] at hd1'
  have hW0 : 0 ≤ δ * T n + |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) :=
    add_nonneg (mul_nonneg hδ hT0) (mul_nonneg (abs_nonneg _) hX0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hW0, one_mul, abs_le]
  have he : hsDefect D chi (δ * hh) n - δ * hsDefect D (chiP D) hh n = chi n - δ * chiP D n := by
    simp only [hsDefect]; ring
  rw [he]
  constructor <;> linarith

/- English proof (translation)
Assume the negation of the conclusion as `hlt'`. Establish `hlt` using `not_le.mp hlt'`. Establish `hF : (0 : ℝ) < ((D + 1).factorial : ℝ)` using `by positivity`. Use `set ε : ℝ := (t₁ - t₂ - s) / ((D + 1).factorial : ℝ) with hε_def`. Establish `hε : 0 < ε` using `div_pos (by linarith) hF`.

Establish `hb` using `((h₁.sub h₂).sub he).def (half_pos hε)`. Take `⟨n, hn, hb', h1⟩` from `(hle.and_eventually (hb.and (eventually_ge_atTop 1))).exists`. Establish `hP : (0 : ℝ) < (n : ℝ) ^ (D + 1)`. Establish `: (1 : ℝ) ≤ n` using `by exact_mod_cast h1`. Check the signs of the components of the expression.

Simplify using `only [Real.norm_eq_abs, abs_of_pos hP] at hb'`. Establish `hb2` using `(abs_le.mp hb').1`. Unfold `hsDefect at hb2`. Establish `key : ε * (n : ℝ) ^ (D + 1) = t₁ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - t₂ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)`. Rewrite using `[hε_def]`.

Clear the denominators using the available nonvanishing facts. Establish `: 0 < ε / 2 * (n : ℝ) ^ (D + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_frequently_le (D : ℕ) (chi₁ chi₂ e : ℕ → ℝ) (t₁ t₂ s : ℝ)
    (h₁ : hsDefect D chi₁ t₁ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (h₂ : hsDefect D chi₂ t₂ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (he : e =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (hle : ∃ᶠ n : ℕ in atTop,
      chi₁ n ≤ chi₂ n + s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) + e n) :
    t₁ ≤ t₂ + s := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  set ε : ℝ := (t₁ - t₂ - s) / ((D + 1).factorial : ℝ) with hε_def
  have hε : 0 < ε := div_pos (by linarith) hF
  have hb := ((h₁.sub h₂).sub he).def (half_pos hε)
  obtain ⟨n, hn, hb', h1⟩ := (hle.and_eventually (hb.and (eventually_ge_atTop 1))).exists
  have hP : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    positivity
  simp only [Real.norm_eq_abs, abs_of_pos hP] at hb'
  have hb2 := (abs_le.mp hb').1
  unfold hsDefect at hb2
  have key : ε * (n : ℝ) ^ (D + 1) = t₁ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - t₂ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
    rw [hε_def]; field_simp
  have : 0 < ε / 2 * (n : ℝ) ^ (D + 1) := by positivity
  linarith

/- English proof (translation)
Establish `h` using `((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left t).mul_isLittleO hr`. Use `h.congr (fun n => ?_) (fun n => by ring)` and prove the remaining obligations. Establish `hD : (0 : ℝ) < (D.factorial : ℝ)` using `by positivity`. Rewrite using `[Nat.factorial_succ]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rank_mul_isLittleO (D : ℕ) (r : ℕ → ℝ) (δ t : ℝ)
    (hr : (fun n : ℕ => r n - δ * (n : ℝ) ^ D / (D.factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ D) :
    (fun n : ℕ => (n : ℝ) * r n * t -
        ((D + 1 : ℝ) * δ * t) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := ((isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).const_mul_left t).mul_isLittleO hr
  refine h.congr (fun n => ?_) (fun n => by ring)
  have hD : (0 : ℝ) < (D.factorial : ℝ) := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
