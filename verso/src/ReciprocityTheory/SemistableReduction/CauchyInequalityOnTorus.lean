import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.ExistsTorusPointOneLeNormSum

namespace ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
Introduce `K _ _ _ K₀ hK₀ n c hc hτ χ`. Assume the negation of the conclusion as `hχ`. Use `push_neg at hχ`. Establish `hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2` using `hc.eventually (gt_mem_nhds (by norm_num))`. Establish `hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite` using `Filter.eventually_cofinite.1 hev`.

Use `set F := hFfin.toFinset with hFdef`. Establish `hχF : χ ∈ F`. Rewrite using `[Set.Finite.mem_toFinset]`. Use `show ¬ ‖c χ‖ < 1 / 2`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨χm, hχmF, hmax⟩` from `F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩`. Establish `hgt : 1 < ‖c χm‖` using `lt_of_lt_of_le hχ (hmax χ hχF)`. Establish `hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖`. Introduce `ψ`. Distinguish the cases in `hψ : ψ ∈ F`.

Conclude with `hmax ψ hψ`. Establish `h2 : ‖c ψ‖ < 1 / 2`. Rewrite `hψ` using `[Set.Finite.mem_toFinset]`. Simplify using `using hψ`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set lam := c χm with hlam`. Establish `hlam0 : lam ≠ 0`. Introduce `h`. Rewrite `hgt` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef`. Establish `ha : ∀ ψ, ‖a ψ‖ ≤ 1`. Introduce `ψ`. Simplify using `only [hadef, norm_div]`. Conclude with `(div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)`.

Establish `ha0 : ‖a χm‖ = 1`. Simplify using `only [hadef, norm_div]`. Conclude with `div_self (norm_ne_zero_iff.2 hlam0)`. Take `⟨τ, hτu, hτ1⟩` from `exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0`. Establish `hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1`.

Introduce `ψ`. Rewrite using `[norm_prod]`. Conclude with `Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]`. Establish `hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun ψ _ => ?_` and prove the remaining obligations. Simplify using `only [hadef]`. Clear the denominators using the available nonvanishing facts. Establish `hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖`. Rewrite using `[hSF, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i)`. Apply `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` to reduce the goal to its premises. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Simplify `hc` using `[norm_mul, hprodnorm]`.

Establish `hsplit` using `hsum.sum_add_tsum_compl (s := F)`. Establish `htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, hprodnorm, mul_one]`. Establish `hψ : (ψ : Fin n → ℤ) ∉ F` using `fun h => ψ.2 (Finset.mem_coe.2 h)`.

Rewrite `hψ` using `[Set.Finite.mem_toFinset]`. Simplify using `only [Set.mem_setOf_eq, not_not] at hψ`. Conclude with `le_of_lt hψ`. Establish `hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠ ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖`. Introduce `h`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `htot` using `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne`. Rewrite `htot` using `[hsplit]`. Establish `h1` using `hτ τ hτu`. Unfold `torusSum at h1`.

Rewrite `h1` using `[htot]`. Establish `h3` using `le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cauchy_inequality_on_torus : CauchyTorusStatement := by
  intro K _ _ _ K₀ hK₀ n c hc hτ χ
  by_contra hχ
  push_neg at hχ
  have hev : ∀ᶠ ψ in Filter.cofinite, ‖c ψ‖ < 1 / 2 := hc.eventually (gt_mem_nhds (by norm_num))
  have hFfin : {ψ | ¬ ‖c ψ‖ < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  set F := hFfin.toFinset with hFdef
  have hχF : χ ∈ F := by
    rw [Set.Finite.mem_toFinset]
    show ¬ ‖c χ‖ < 1 / 2
    linarith
  obtain ⟨χm, hχmF, hmax⟩ := F.exists_max_image (fun ψ => ‖c ψ‖) ⟨χ, hχF⟩
  have hgt : 1 < ‖c χm‖ := lt_of_lt_of_le hχ (hmax χ hχF)
  have hglob : ∀ ψ, ‖c ψ‖ ≤ ‖c χm‖ := by
    intro ψ
    by_cases hψ : ψ ∈ F
    · exact hmax ψ hψ
    · have h2 : ‖c ψ‖ < 1 / 2 := by
        rw [Set.Finite.mem_toFinset] at hψ
        simpa using hψ
      linarith
  set lam := c χm with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hgt
    linarith
  set a : (Fin n → ℤ) → K := fun ψ => c ψ / lam with hadef
  have ha : ∀ ψ, ‖a ψ‖ ≤ 1 := by
    intro ψ
    simp only [hadef, norm_div]
    exact (div_le_one (norm_pos_iff.2 hlam0)).2 (hglob ψ)
  have ha0 : ‖a χm‖ = 1 := by
    simp only [hadef, norm_div]
    exact div_self (norm_ne_zero_iff.2 hlam0)
  obtain ⟨τ, hτu, hτ1⟩ := exists_torus_point_one_le_norm_sum K₀ hK₀ F a ha χm hχmF ha0
  have hprodnorm : ∀ ψ : Fin n → ℤ, ‖∏ i, τ i ^ ψ i‖ = 1 := by
    intro ψ
    rw [norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, (hτu i).2, one_zpow]
  have hSF : ∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i = lam * ∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    simp only [hadef]
    field_simp
  have hSFn : ‖lam‖ ≤ ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ := by
    rw [hSF, norm_mul]
    calc ‖lam‖ = ‖lam‖ * 1 := (mul_one _).symm
      _ ≤ ‖lam‖ * ‖∑ ψ ∈ F, a ψ * ∏ i, τ i ^ ψ i‖ := mul_le_mul_of_nonneg_left hτ1 (norm_nonneg _)
  have hsum : Summable (fun ψ => c ψ * ∏ i, τ i ^ ψ i) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_mul, hprodnorm] using hc
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have htail : ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by norm_num) fun ψ => ?_
    rw [norm_mul, hprodnorm, mul_one]
    have hψ : (ψ : Fin n → ℤ) ∉ F := fun h => ψ.2 (Finset.mem_coe.2 h)
    rw [Set.Finite.mem_toFinset] at hψ
    simp only [Set.mem_setOf_eq, not_not] at hψ
    exact le_of_lt hψ
  have hne : ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖ ≠
      ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖ := by
    intro h
    linarith
  have htot := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [hsplit] at htot
  have h1 := hτ τ hτu
  unfold torusSum at h1
  rw [htot] at h1
  have h3 := le_max_left ‖∑ ψ ∈ F, c ψ * ∏ i, τ i ^ ψ i‖
    ‖∑' ψ : ↑((F : Set (Fin n → ℤ))ᶜ), c ψ * ∏ i, τ i ^ (ψ : Fin n → ℤ) i‖
  linarith

end ReciprocityTheory.MultiplicativeHeights
