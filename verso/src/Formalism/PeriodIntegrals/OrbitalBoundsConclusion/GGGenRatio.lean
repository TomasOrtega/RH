import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GenericRatioBound.GenericRatioOfBound

/- English proof (translation)
Unfold `Formalism.L2.SG.GGMirabolic.GenericRatioOfBound`. Introduce `hMir hCard`. Unfold `Formalism.L2.SG.GGMirabolic.GenericRatio`. Introduce `F _ _ k ψ₀ hψ V _ _ _ π hirr hgen`. Establish `hb` using `hMir F k ψ₀ hψ V π hirr hgen`.

Rewrite using `[hCard F k]`. Establish `hq : 1 < Fintype.card F` using `Fintype.one_lt_card`. Establish `hqR : (1 : ℝ) < (Fintype.card F : ℝ)` using `by exact_mod_cast hq`. Establish `hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i`. Introduce `i hi`.

Establish `hi1 : i ≠ 0`. Simplify using `only [Finset.mem_Ico] at hi`. Use linear arithmetic over natural numbers and integers. Conclude with `one_lt_pow₀ hqR hi1`. Establish `hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2`.

Rewrite using `[← Finset.sum_range_id]`. Break down `Nat.eq_zero_or_pos k with hk | hk` into its components or cases. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]`.

Simplify using the standard rewrite rules. Establish `hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1)` using `Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)`. Establish `hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ) = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1)`. Rewrite using `[Nat.cast_prod]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]`. Establish `hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ)`. Rewrite using `[← hcast]`. Conclude with `hb` after adjusting the coercions.

Establish `hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹ = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1)`. Rewrite using `[← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Establish `h1` using `hx i hi`.

Establish `h0 : (Fintype.card F : ℝ) ^ i ≠ 0` using `(lt_trans one_pos h1).ne'`. Establish `h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0` using `(sub_pos.mpr h1).ne'`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hR, Nat.cast_pow]`. Use `gcongr`.

Apply the tactic sequence `all_goals first`. Consider the case `exact hPD`. Consider the case `exact hP.le`. Consider the case `exact hP`. Consider the case `positivity`.
-/
theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
