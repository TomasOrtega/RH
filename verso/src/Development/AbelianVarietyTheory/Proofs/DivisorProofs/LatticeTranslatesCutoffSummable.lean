import Mathlib

open SchwartzMap

noncomputable section

namespace GlobalTheory.SchwartzTranslateSum

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)` and prove the remaining obligations. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using the standard rewrite rules. Establish `h0 : 0 < ‖z‖` using `norm_pos_iff.2 hz`.

Simplify using `only [hz, if_false, add_zero]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem summable_one_add_norm_inv_pow' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by
  classical
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv Λ N hN).add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

/- English proof (translation)
Take `⟨R, hR⟩` from `hh.isCompact.isBounded.subset_closedBall (0 : V)`. Use `set N := Module.finrank ℤ Λ + 1 with hNdef`. Establish `hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N` using `summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)`. Use `set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f with hSdef`. Use `set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h with hAdef`.

Use `set R' := max R 0 with hR'def`. Establish `hR'0 : 0 ≤ R'` using `le_max_right _ _`. Use `set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef`. Establish `hS0 : 0 ≤ S` using `apply_nonneg _ _`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg fun i _ => by positivity`.

Establish `hD0 : 0 ≤ D` using `by positivity`. Use `clear_value D A S R' N`. Use `(hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)` and prove the remaining obligations. Use `SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)` and prove the remaining obligations. Establish `hfun : (u l : V → ℂ) = fun y => h (y + l) * f y` using `funext (hu l)`.

Rewrite using `[hfun]`. Establish `hsh : ContDiff ℝ n (fun y => h (y + (l : V)))` using `((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)`. Establish `hsf : ContDiff ℝ n (f : V → ℂ)` using `(f.smooth ⊤).of_le (by exact_mod_cast le_top)`. Establish `hleib` using `norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl`. Rewrite `hleib` using `[iteratedFDeriv_comp_add_right]`.

Distinguish the cases in `hx : x + (l : V) ∈ tsupport h`. Establish `hxl : ‖x + (l : V)‖ ≤ R'`. Use `hR hx` as an intermediate fact. Rewrite `this` using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `this.trans (hR'def ▸ le_max_left _ _)`.

Establish `hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖)`. Establish `: ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖`. Combine the equalities or inequalities in the displayed calculation. Establish `hn' : ‖l‖ = ‖(l : V)‖` using `rfl`. Use polynomial arithmetic with `[norm_nonneg x]`.

Establish `hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N`. Introduce `m hm`. Establish `h1` using `one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m) le_rfl hm f x`. Establish `h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S` using `by rw [hSdef]; exact h1`. Establish `hpos : 0 < (1 + ‖l‖) ^ N` using `by positivity`.

Rewrite using `[inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[norm_nonneg x]`. Use `_ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by`. Rewrite using `[mul_pow, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr`. Use `_ = D := by rw [hDdef]; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring`.

Use `_ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h * (D * ((1 + ‖l‖)⁻¹) ^ N) := by`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity)) (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)`. Use `_ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by`. Rewrite using `[hAdef, Finset.sum_mul, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0` using `fun i => Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)`. Simplify using `only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib`. Establish `: ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0` using `le_antisymm hleib (norm_nonneg _)`. Rewrite using `[this, mul_zero]`.

Conclude with `mul_nonneg (mul_nonneg hA0 hD0) (by positivity)`.
-/
theorem summable_seminorm_mul_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (h f : SchwartzMap V ℂ) (hh : HasCompactSupport h)
    (u : Λ → SchwartzMap V ℂ) (hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x) (k n : ℕ) :
    Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall (0 : V)
  set N := Module.finrank ℤ Λ + 1 with hNdef
  have hw : Summable fun l : Λ => ((1 + ‖l‖)⁻¹) ^ N :=
    summable_one_add_norm_inv_pow' Λ (Nat.lt_succ_self _)
  set S := (Finset.Iic (k + N, n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℂ m.1 m.2) f
    with hSdef
  set A := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h
    with hAdef
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set D := (1 + R') ^ N * 2 ^ (k + N) * S with hDdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  have hD0 : 0 ≤ D := by positivity
  clear_value D A S R' N
  refine (hw.mul_left (A * D)).of_nonneg_of_le (fun l => apply_nonneg _ _) (fun l => ?_)
  refine SchwartzMap.seminorm_le_bound ℂ k n (u l) (by positivity) (fun x => ?_)
  have hfun : (u l : V → ℂ) = fun y => h (y + l) * f y := funext (hu l)
  rw [hfun]
  have hsh : ContDiff ℝ n (fun y => h (y + (l : V))) :=
    ((h.smooth ⊤).of_le (by exact_mod_cast le_top)).comp (contDiff_id.add contDiff_const)
  have hsf : ContDiff ℝ n (f : V → ℂ) := (f.smooth ⊤).of_le (by exact_mod_cast le_top)
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsh hsf x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_add_right] at hleib
  by_cases hx : x + (l : V) ∈ tsupport h
  · have hxl : ‖x + (l : V)‖ ≤ R' := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (hR'def ▸ le_max_left _ _)
    have hl : 1 + ‖l‖ ≤ (1 + R') * (1 + ‖x‖) := by
      have : ‖(l : V)‖ ≤ ‖x + (l : V)‖ + ‖x‖ := by
        calc ‖(l : V)‖ = ‖(x + (l : V)) - x‖ := by simp
          _ ≤ ‖x + (l : V)‖ + ‖x‖ := norm_sub_le _ _
      have hn' : ‖l‖ = ‖(l : V)‖ := rfl
      nlinarith [norm_nonneg x]
    have hB : ∀ m ≤ n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ D * ((1 + ‖l‖)⁻¹) ^ N := by
      intro m hm
      have h1 := one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + N, n)) (k := k + N) (n := m)
        le_rfl hm f x
      have h1' : (1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖ ≤ 2 ^ (k + N) * S := by rw [hSdef]; exact h1
      have hpos : 0 < (1 + ‖l‖) ^ N := by positivity
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ * (1 + ‖l‖) ^ N
          ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ * ((1 + R') * (1 + ‖x‖)) ^ N := by
            gcongr
            linarith [norm_nonneg x]
        _ = (1 + R') ^ N * ((1 + ‖x‖) ^ (k + N) * ‖iteratedFDeriv ℝ m f x‖) := by
            rw [mul_pow, pow_add]; ring
        _ ≤ (1 + R') ^ N * (2 ^ (k + N) * S) := by gcongr
        _ = D := by rw [hDdef]; ring
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖
        ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i h (x + l)‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i h (x + l)‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i h *
            (D * ((1 + ‖l‖)⁻¹) ^ N) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (mul_le_mul_of_nonneg_left
              (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ h i _) (by positivity))
              (hB _ (Nat.sub_le _ _)) (by positivity) (by positivity)
      _ = A * D * ((1 + ‖l‖)⁻¹) ^ N := by
            rw [hAdef, Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
  · have hz : ∀ i, iteratedFDeriv ℝ i h (x + l) = 0 := fun i =>
      Function.notMem_support.1 fun hm => hx (support_iteratedFDeriv_subset i hm)
    simp only [hz, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero] at hleib
    have : ‖iteratedFDeriv ℝ n (fun y => h (y + (l : V)) * f y) x‖ = 0 :=
      le_antisymm hleib (norm_nonneg _)
    rw [this, mul_zero]
    exact mul_nonneg (mul_nonneg hA0 hD0) (by positivity)

end GlobalTheory.SchwartzTranslateSum
