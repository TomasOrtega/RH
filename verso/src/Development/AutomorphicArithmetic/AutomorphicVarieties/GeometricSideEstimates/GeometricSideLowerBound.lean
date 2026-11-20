import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `A V _ _ _ φ hs v hv`. Establish `ht : 0 < ‖φ v‖` using `norm_pos_iff.mpr hv`. Use `set t := ‖φ v‖ with htdef`. Establish `hn : ∀ k : ℕ, ‖φ (k • v)‖ = k * t`. Introduce `k`.

Rewrite using `[map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]`. Establish `hinj : Function.Injective (fun k : ℕ => k • v)`. Introduce `k l h`. Establish `h1 : (k : ℝ) * t = l * t`. Rewrite using `[← hn k, ← hn l]`.

Conclude with `congrArg (fun x => ‖φ x‖) h`. Conclude with `mul_right_cancel₀ ht.ne' h1` after adjusting the coercions. Use `set n := ⌊1 / t⌋₊ with hndef`. Establish `h1 : 1 / t < n + 1` using `Nat.lt_floor_add_one _`. Establish `h2 : (n : ℝ) ≤ 1 / t` using `Nat.floor_le (by positivity)`.

Establish `h3 : ∑ x ∈ (Finset.range (n + 1)).image (fun k : ℕ => k • v), Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2)` using `hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)`. Rewrite `h3` using `[Finset.sum_image (fun a _ b _ h => hinj h)]`. Establish `h4 : ∑ _k ∈ Finset.range (n + 1), Real.exp (-Real.pi) ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (-Real.pi * ‖φ (k • v)‖ ^ 2)`. Use `Finset.sum_le_sum fun k hk => Real.exp_le_exp.mpr ?_` and prove the remaining obligations. Establish `hk' : (k : ℝ) ≤ n` using `by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`.

Establish `h5 : (k : ℝ) * t ≤ 1`. Use `hk'.trans h2` as an intermediate fact. Rewrite `this` using `[le_div_iff₀ ht]`. Then use the resulting hypothesis. Establish `h6 : 0 ≤ (k : ℝ) * t` using `by positivity`. Establish `h7 : ((k : ℝ) * t) ^ 2 ≤ 1` using `by nlinarith`.

Rewrite using `[hn]`. Use polynomial arithmetic with `[Real.pi_pos]`. Rewrite `h4` using `[Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Move the coercions through the operations in `at h4`. Establish `h8 : 1 ≤ t * (n + 1)`.

Rewrite `h1` using `[div_lt_iff₀ ht]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h9` using `mul_le_mul_of_nonneg_left (h4.trans h3) ht.le`. Establish `h10` using `mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-Real.pi)).le`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.geometric_side_lower_bound :
    ThetaLow := by
  classical
  intro A V _ _ _ φ hs v hv
  have ht : 0 < ‖φ v‖ := norm_pos_iff.mpr hv
  set t := ‖φ v‖ with htdef
  have hn : ∀ k : ℕ, ‖φ (k • v)‖ = k * t := by
    intro k
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
  have hinj : Function.Injective (fun k : ℕ => k • v) := by
    intro k l h
    have h1 : (k : ℝ) * t = l * t := by
      rw [← hn k, ← hn l]
      exact congrArg (fun x => ‖φ x‖) h
    exact_mod_cast mul_right_cancel₀ ht.ne' h1
  set n := ⌊1 / t⌋₊ with hndef
  have h1 : 1 / t < n + 1 := Nat.lt_floor_add_one _
  have h2 : (n : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
  have h3 : ∑ x ∈ (Finset.range (n + 1)).image (fun k : ℕ => k • v), Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    hs.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun a _ b _ h => hinj h)] at h3
  have h4 : ∑ _k ∈ Finset.range (n + 1), Real.exp (-Real.pi) ≤
      ∑ k ∈ Finset.range (n + 1), Real.exp (-Real.pi * ‖φ (k • v)‖ ^ 2) := by
    refine Finset.sum_le_sum fun k hk => Real.exp_le_exp.mpr ?_
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h5 : (k : ℝ) * t ≤ 1 := by
      have := hk'.trans h2
      rwa [le_div_iff₀ ht] at this
    have h6 : 0 ≤ (k : ℝ) * t := by positivity
    have h7 : ((k : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
    rw [hn]
    nlinarith [Real.pi_pos]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
  push_cast at h4
  have h8 : 1 ≤ t * (n + 1) := by
    rw [div_lt_iff₀ ht] at h1
    linarith
  have h9 := mul_le_mul_of_nonneg_left (h4.trans h3) ht.le
  have h10 := mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-Real.pi)).le
  calc Real.exp (-Real.pi) = 1 * Real.exp (-Real.pi) := (one_mul _).symm
    _ ≤ t * (n + 1) * Real.exp (-Real.pi) := h10
    _ = t * ((n + 1) * Real.exp (-Real.pi)) := by ring
    _ ≤ _ := h9
