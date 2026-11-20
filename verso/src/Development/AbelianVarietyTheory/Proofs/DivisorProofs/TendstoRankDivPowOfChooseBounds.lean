import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D))`. Use `((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D` as an intermediate fact. Simplify using `using this`. Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with m hm`.

Establish `hm' : (m : ℝ) ≠ 0` using `by exact_mod_cast hm.ne'`. Rewrite using `[← div_pow]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_div_add_const_pow_div_pow (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp

/- English proof (translation)
Use `choose! c c' hc using h`. Use `set C := ∑ s ∈ Finset.range e, c s with hC`. Use `set C' := ∑ s ∈ Finset.range e, c' s with hC'`. Establish `hcC : ∀ s, s < e → c s ≤ C` using `fun s hs => Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)`. Establish `hcC' : ∀ s, s < e → c' s ≤ C'` using `fun s hs => Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)`.

Establish `heR : (0 : ℝ) < e` using `by exact_mod_cast he`. Establish `hDf : (0 : ℝ) < D.factorial` using `by exact_mod_cast D.factorial_pos`. Establish `hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial * (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial)))`. Introduce `K`. Use `(tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[div_pow, one_pow]`. Clear the denominators using the available nonvanishing facts. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm`.

Establish `hmpos : (0 : ℝ) < m` using `by exact_mod_cast (show 0 < m by omega)`. Establish `hs : m % e < e` using `Nat.mod_lt _ he`. Establish `hm_eq : e * (m / e) + m % e = m` using `Nat.div_add_mod m e`. Establish `hqC : C ≤ m / e` using `(Nat.le_div_iff_mul_le he).2 (by nlinarith)`. Establish `hcs` using `hcC (m % e) hs`.

Establish `h1` using `(hc (m % e) hs (m / e - c (m % e))).1`. Rewrite `h1` using `[Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq]`. Establish `h2` using `Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)`. Establish `h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1` using `by omega`. Rewrite `h2` using `[h3]`.

Establish `hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ)` using `by exact_mod_cast hm_eq.symm`. Establish `hsR : ((m % e : ℕ) : ℝ) < e` using `by exact_mod_cast hs`. Establish `hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1`. Rewrite using `[div_lt_iff₀ heR]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hge : (C : ℝ) ≤ (m : ℝ) / e`. Rewrite using `[le_div_iff₀ heR]`. Establish `: ((e * C : ℕ) : ℝ) ≤ m` using `by exact_mod_cast (show e * C ≤ m by omega)`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hcsR : (c (m % e) : ℝ) ≤ C` using `by exact_mod_cast hcs`. Establish `hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ)`. Rewrite using `[Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith`. Establish `hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ)` using `by linarith`. Establish `hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Use `filter_upwards [eventually_ge_atTop 1] with m hm`. Establish `hmpos : (0 : ℝ) < m` using `by exact_mod_cast (show 0 < m by omega)`. Establish `hs : m % e < e` using `Nat.mod_lt _ he`.

Establish `hm_eq : e * (m / e) + m % e = m` using `Nat.div_add_mod m e`. Establish `h1` using `(hc (m % e) hs (m / e)).2`. Rewrite `h1` using `[hm_eq]`. Establish `h2` using `Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)`. Establish `hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ)` using `by exact_mod_cast hm_eq.symm`.

Establish `hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e`. Rewrite using `[le_div_iff₀ heR]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcsR : (c' (m % e) : ℝ) ≤ C'` using `by exact_mod_cast hcC' (m % e) hs`.

Establish `hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ)` using `by push_cast; linarith`. Establish `hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  choose! c c' hc using h
  set C := ∑ s ∈ Finset.range e, c s with hC
  set C' := ∑ s ∈ Finset.range e, c' s with hC'
  have hcC : ∀ s, s < e → c s ≤ C := fun s hs =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have hcC' : ∀ s, s < e → c' s ≤ C' := fun s hs =>
    Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial *
      (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
    intro K
    have := (tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)
    convert this using 2
    rw [div_pow, one_pow]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have hqC : C ≤ m / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
    have hcs := hcC (m % e) hs
    have h1 := (hc (m % e) hs (m / e - c (m % e))).1
    rw [Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq] at h1
    have h2 := Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)
    have h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1 := by omega
    rw [h3] at h2
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hsR : ((m % e : ℕ) : ℝ) < e := by exact_mod_cast hs
    have hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ heR]; nlinarith
    have hge : (C : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]
      have : ((e * C : ℕ) : ℝ) ≤ m := by exact_mod_cast (show e * C ≤ m by omega)
      push_cast at this; linarith
    have hcsR : (c (m % e) : ℝ) ≤ C := by exact_mod_cast hcs
    have hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ) := by linarith
    have hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m := by
      calc (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D
          ≤ (δ : ℝ) / D.factorial * (((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D := by gcongr
        _ = (δ : ℝ) * ((((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D / D.factorial) := by ring
        _ ≤ (δ : ℝ) * ((m / e - c (m % e) + D).choose D : ℝ) := by gcongr
        _ ≤ r m := by exact_mod_cast h1
    calc (δ : ℝ) / D.factorial * (((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D)
        = (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D := by ring
      _ ≤ (r m : ℝ) / (m : ℝ) ^ D := by gcongr
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have h1 := (hc (m % e) hs (m / e)).2
    rw [hm_eq] at h1
    have h2 := Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]; nlinarith
    have hcsR : (c' (m % e) : ℝ) ≤ C' := by exact_mod_cast hcC' (m % e) hs
    have hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D := by
      calc (r m : ℝ) ≤ (δ : ℝ) * ((m / e + c' (m % e) + D).choose D : ℝ) := by exact_mod_cast h1
        _ ≤ (δ : ℝ) * (((m / e + c' (m % e) + D : ℕ) : ℝ) ^ D / D.factorial) := by gcongr
        _ = (δ : ℝ) / D.factorial * (((m / e + c' (m % e) + D : ℕ) : ℝ)) ^ D := by ring
        _ ≤ _ := by gcongr
    calc (r m : ℝ) / (m : ℝ) ^ D
        ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D / (m : ℝ) ^ D := by gcongr
      _ = _ := by ring

end GlobalTheory
