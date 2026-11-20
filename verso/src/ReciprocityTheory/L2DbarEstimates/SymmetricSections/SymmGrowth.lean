import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Introduce `n M z u R δ hR hdeg k w`. Establish `hfin : (z ⁻¹' {w}).Finite` using `Set.finite_of_encard_le_coe (hdeg w)`. Establish `hcard : hfin.toFinset.card ≤ δ`. Use `hdeg w` as an intermediate fact. Rewrite `this` using `[← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard]`.

Conclude with `this` after adjusting the coercions. Unfold `fiberSymm fiberVals`. Rewrite using `[dif_pos hfin, Finset.esymm_map_val]`. Establish `hB : 0 ≤ max (R w) 0` using `le_max_right _ _`. Establish `hu : ∀ y ∈ hfin.toFinset, ‖u y‖ ≤ max (R w) 0`.

Introduce `y hy`. Rewrite `hy` using `[Set.Finite.mem_toFinset]`. Establish `hy' : z y = w` using `hy`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht` using `[Finset.mem_powersetCard]`. Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = ((hfin.toFinset.powersetCard k).card : ℝ) * (max (R w) 0) ^ k := by`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `_ ≤ 2 ^ δ * (max (R w) 0) ^ k := by`. Apply `mul_le_mul_of_nonneg_right _ (pow_nonneg hB k)` to reduce the goal to its premises. Rewrite using `[Finset.card_powersetCard]`.

Establish `h1` using `Nat.choose_le_two_pow hfin.toFinset.card k`. Establish `h2 : 2 ^ hfin.toFinset.card ≤ 2 ^ δ` using `Nat.pow_le_pow_right (by norm_num) hcard`. Conclude with `h1.trans h2` after adjusting the coercions.
-/
theorem symmGrowth : symmGrowthStatement.{u} := by
  intro n M z u R δ hR hdeg k w
  have hfin : (z ⁻¹' {w}).Finite := Set.finite_of_encard_le_coe (hdeg w)
  have hcard : hfin.toFinset.card ≤ δ := by
    have := hdeg w
    rw [← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  unfold fiberSymm fiberVals
  rw [dif_pos hfin, Finset.esymm_map_val]
  have hB : 0 ≤ max (R w) 0 := le_max_right _ _
  have hu : ∀ y ∈ hfin.toFinset, ‖u y‖ ≤ max (R w) 0 := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    have hy' : z y = w := hy
    calc ‖u y‖ ≤ R (z y) := hR y
      _ = R w := by rw [hy']
      _ ≤ max (R w) 0 := le_max_left _ _
  calc ‖∑ t ∈ hfin.toFinset.powersetCard k, t.prod u‖
      ≤ ∑ t ∈ hfin.toFinset.powersetCard k, ‖t.prod u‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ hfin.toFinset.powersetCard k, (max (R w) 0) ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_powersetCard] at ht
        rw [norm_prod]
        calc ∏ y ∈ t, ‖u y‖ ≤ ∏ _y ∈ t, max (R w) 0 :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun y hy => hu y (ht.1 hy))
          _ = (max (R w) 0) ^ k := by rw [Finset.prod_const, ht.2]
    _ = ((hfin.toFinset.powersetCard k).card : ℝ) * (max (R w) 0) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ δ * (max (R w) 0) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB k)
        rw [Finset.card_powersetCard]
        have h1 := Nat.choose_le_two_pow hfin.toFinset.card k
        have h2 : 2 ^ hfin.toFinset.card ≤ 2 ^ δ := Nat.pow_le_pow_right (by norm_num) hcard
        exact_mod_cast h1.trans h2

end ReciprocityTheory.L2DbarEstimates.Norm
