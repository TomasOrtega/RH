import Mathlib
open SchwartzMap Filter Topology
open scoped Nat

namespace GlobalTheory

/- English proof (translation)
Use `set L : V →L[ℝ] (Fin j → V) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ V) with hL`. Establish `hLn : ‖L‖ ≤ 1` using `ContinuousLinearMap.norm_pi_le_of_le (fun _ => ContinuousLinearMap.norm_id_le) zero_le_one`. Establish `hfun : (fun y => f (fun _ => y)) = (⇑f) ∘ ⇑L` using `rfl`. Rewrite using `[hfun, L.iteratedFDeriv_comp_right (f.contDiff (n := ⊤)) x (by exact_mod_cast le_top)]`. Establish `hLx : ‖L x‖ ≤ ‖x‖`.

Use `L.le_opNorm x` as an intermediate fact. Use polynomial arithmetic with `[norm_nonneg x]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLn)`. Use `_ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖L x‖ ^ (j - a) := by`.

Rewrite using `[mul_one]`. Use `f.norm_iteratedFDeriv_le a (L x)` as an intermediate fact. Simplify using `using this`. Use `_ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖x‖ ^ (j - a) := by gcongr`.
-/
theorem norm_iteratedFDeriv_diag_le {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => V) F)
    (a : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ a (fun y => f (fun _ => y)) x‖ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖x‖ ^ (j - a) := by
  set L : V →L[ℝ] (Fin j → V) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ V) with hL
  have hLn : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_pi_le_of_le (fun _ => ContinuousLinearMap.norm_id_le) zero_le_one
  have hfun : (fun y => f (fun _ => y)) = (⇑f) ∘ ⇑L := rfl
  rw [hfun, L.iteratedFDeriv_comp_right (f.contDiff (n := ⊤)) x (by exact_mod_cast le_top)]
  have hLx : ‖L x‖ ≤ ‖x‖ := by
    have := L.le_opNorm x
    nlinarith [norm_nonneg x]
  calc ‖(iteratedFDeriv ℝ a (⇑f) (L x)).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖iteratedFDeriv ℝ a (⇑f) (L x)‖ * ∏ _i : Fin a, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ a (⇑f) (L x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
    _ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖L x‖ ^ (j - a) := by
        rw [mul_one]
        have := f.norm_iteratedFDeriv_le a (L x)
        simpa using this
    _ ≤ (j.descFactorial a : ℝ) * ‖f‖ * ‖x‖ ^ (j - a) := by
        gcongr

/- English proof (translation)
Introduce `V _ _ _ ψ A ρ hψ m a x`. Establish `hcd : ∀ j ∈ Finset.range (m + 1), ContDiff ℝ (a : ℕ) (fun y : V => ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y))`. Introduce `j _`. Establish `h1 : ContDiff ℝ (a : ℕ) (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y))` using `(iteratedFDeriv ℝ j ψ 0).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)`. Conclude with `h1.const_smul _`.

Rewrite using `[iteratedFDeriv_sum hcd, Finset.sum_apply]`. Use `set t := |ρ| * ‖x‖ with ht`. Establish `ht0 : 0 ≤ t` using `by positivity`. Use `set h : ℕ → ℝ := fun j => if a ≤ j then |A| * |ρ| ^ a * (t ^ (j - a) / ((j - a) ! : ℝ)) else 0 with hh`. Establish `hterm : ∀ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ a (fun y : V => ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ ≤ h j`.

Introduce `j _`. Establish `hsm : (fun y : V => ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) = ((j ! : ℝ))⁻¹ • (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y))` using `rfl`. Rewrite using `[hsm, iteratedFDeriv_const_smul_apply (f := fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) ((((iteratedFDeriv ℝ j ψ 0).contDiff (n := ⊤)).comp (contDiff_pi.2 fun _ => contDiff_id)).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]`. Establish `hb` using `norm_iteratedFDeriv_diag_le (iteratedFDeriv ℝ j ψ 0) a x`. Establish `hM : ‖iteratedFDeriv ℝ j ψ 0‖ ≤ |A| * |ρ| ^ j`.

Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ‖((j ! : ℝ))⁻¹‖ = ((j ! : ℝ))⁻¹`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Rewrite using `[hinv]`. Distinguish the cases in `haj : a ≤ j`.

Simplify using `only [hh, if_pos haj]`. Establish `hfac : ((j ! : ℝ))⁻¹ * (j.descFactorial a : ℝ) = (((j - a) ! : ℝ))⁻¹`. Use `Nat.factorial_mul_descFactorial haj` as an intermediate fact. Establish `hpos : (0 : ℝ) < ((j - a) ! : ℝ)` using `by positivity`. Establish `hpos2 : (0 : ℝ) < (j ! : ℝ)` using `by positivity`.

Clear the denominators using the available nonvanishing facts. Use `norm_cast`. Rewrite using `[mul_comm]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hfac]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (((j - a) ! : ℝ))⁻¹ * (|A| * |ρ| ^ j) * ‖x‖ ^ (j - a) := by gcongr`. Use `_ = |A| * |ρ| ^ a * (t ^ (j - a) / ((j - a) ! : ℝ)) := by`. Establish `: j = a + (j - a)` using `by omega`.

Rewrite using `[ht, mul_pow]`. Use `conv_lhs => rw [this, pow_add]`. Rewrite using `[show a + (j - a) - a = j - a by omega]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hh, if_neg haj]`.

Establish `hz : j.descFactorial a = 0` using `Nat.descFactorial_eq_zero_iff_lt.2 (by omega)`. Rewrite `hb` using `[hz, Nat.cast_zero, zero_mul, zero_mul]`. Establish `: ‖iteratedFDeriv ℝ a (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ = 0` using `le_antisymm hb (norm_nonneg _)`. Rewrite using `[this, mul_zero]`. Establish `hh0 : ∀ j, 0 ≤ h j`.

Apply the tactic sequence `intro j; simp only [hh]; split_ifs <;> positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_range_add]`. Establish `: ∑ j ∈ Finset.range a, h j = 0` using `Finset.sum_eq_zero (fun j hj => by`. Establish `hja` using `Finset.mem_range.1 hj`.

Simplify using `only [hh]`. Rewrite using `[if_neg (by omega)])`. Rewrite using `[this, zero_add]`. Use `_ = |A| * |ρ| ^ a * ∑ i ∈ Finset.range (m + 1), t ^ i / (i ! : ℝ) := by`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `only [hh, if_pos (Nat.le_add_right a i), Nat.add_sub_cancel_left]`. Use `_ ≤ |A| * |ρ| ^ a * Real.exp t := by gcongr`. Conclude with `Real.sum_le_exp_of_nonneg ht0 _`.
-/
theorem taylorPoly_iteratedFDeriv_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ (m a : ℕ) (x : V), ‖iteratedFDeriv ℝ a (fun y => ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ ≤ |A| * |ρ| ^ a * Real.exp (|ρ| * ‖x‖) := by
  intro V _ _ _ ψ A ρ hψ m a x
  have hcd : ∀ j ∈ Finset.range (m + 1), ContDiff ℝ (a : ℕ) (fun y : V =>
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) := by
    intro j _
    have h1 : ContDiff ℝ (a : ℕ) (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) :=
      (iteratedFDeriv ℝ j ψ 0).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    exact h1.const_smul _
  rw [iteratedFDeriv_sum hcd, Finset.sum_apply]
  set t := |ρ| * ‖x‖ with ht
  have ht0 : 0 ≤ t := by positivity

  set h : ℕ → ℝ := fun j => if a ≤ j then |A| * |ρ| ^ a * (t ^ (j - a) / ((j - a) ! : ℝ)) else 0 with hh
  have hterm : ∀ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ a (fun y : V =>
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ ≤ h j := by
    intro j _
    have hsm : (fun y : V => ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y))
        = ((j ! : ℝ))⁻¹ • (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) := rfl
    rw [hsm, iteratedFDeriv_const_smul_apply (f := fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y))
      ((((iteratedFDeriv ℝ j ψ 0).contDiff (n := ⊤)).comp (contDiff_pi.2 fun _ => contDiff_id)).contDiffAt.of_le
        (by exact_mod_cast le_top)), norm_smul]
    have hb := norm_iteratedFDeriv_diag_le (iteratedFDeriv ℝ j ψ 0) a x
    have hM : ‖iteratedFDeriv ℝ j ψ 0‖ ≤ |A| * |ρ| ^ j := by
      calc _ ≤ A * ρ ^ j := hψ j 0
        _ ≤ |A * ρ ^ j| := le_abs_self _
        _ = |A| * |ρ| ^ j := by rw [abs_mul, abs_pow]
    have hinv : ‖((j ! : ℝ))⁻¹‖ = ((j ! : ℝ))⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hinv]
    by_cases haj : a ≤ j
    · simp only [hh, if_pos haj]
      have hfac : ((j ! : ℝ))⁻¹ * (j.descFactorial a : ℝ) = (((j - a) ! : ℝ))⁻¹ := by
        have := Nat.factorial_mul_descFactorial haj
        have hpos : (0 : ℝ) < ((j - a) ! : ℝ) := by positivity
        have hpos2 : (0 : ℝ) < (j ! : ℝ) := by positivity
        field_simp
        norm_cast
        rw [mul_comm]
        exact this
      calc ((j ! : ℝ))⁻¹ * ‖iteratedFDeriv ℝ a (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖
          ≤ ((j ! : ℝ))⁻¹ * ((j.descFactorial a : ℝ) * ‖iteratedFDeriv ℝ j ψ 0‖ * ‖x‖ ^ (j - a)) := by
            gcongr
        _ = (((j - a) ! : ℝ))⁻¹ * ‖iteratedFDeriv ℝ j ψ 0‖ * ‖x‖ ^ (j - a) := by
            rw [← hfac]; ring
        _ ≤ (((j - a) ! : ℝ))⁻¹ * (|A| * |ρ| ^ j) * ‖x‖ ^ (j - a) := by gcongr
        _ = |A| * |ρ| ^ a * (t ^ (j - a) / ((j - a) ! : ℝ)) := by
            have : j = a + (j - a) := by omega
            rw [ht, mul_pow]
            conv_lhs => rw [this, pow_add]
            rw [show a + (j - a) - a = j - a by omega]
            ring
    · simp only [hh, if_neg haj]
      have hz : j.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [hz, Nat.cast_zero, zero_mul, zero_mul] at hb
      have : ‖iteratedFDeriv ℝ a (fun y : V => iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ = 0 :=
        le_antisymm hb (norm_nonneg _)
      rw [this, mul_zero]
  have hh0 : ∀ j, 0 ≤ h j := by
    intro j; simp only [hh]; split_ifs <;> positivity
  calc _ ≤ ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ a (fun y : V =>
        ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), h j := Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.range (a + (m + 1)), h j :=
        Finset.sum_le_sum_of_subset_of_nonneg (by intro y hy; simp only [Finset.mem_range] at hy ⊢; omega) (fun j _ _ => hh0 j)
    _ = ∑ i ∈ Finset.range (m + 1), h (a + i) := by
        rw [Finset.sum_range_add]
        have : ∑ j ∈ Finset.range a, h j = 0 :=
          Finset.sum_eq_zero (fun j hj => by
            have hja := Finset.mem_range.1 hj
            simp only [hh]
            rw [if_neg (by omega)])
        rw [this, zero_add]
    _ = |A| * |ρ| ^ a * ∑ i ∈ Finset.range (m + 1), t ^ i / (i ! : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hh, if_pos (Nat.le_add_right a i), Nat.add_sub_cancel_left]
    _ ≤ |A| * |ρ| ^ a * Real.exp t := by
        gcongr
        exact Real.sum_le_exp_of_nonneg ht0 _

end GlobalTheory
