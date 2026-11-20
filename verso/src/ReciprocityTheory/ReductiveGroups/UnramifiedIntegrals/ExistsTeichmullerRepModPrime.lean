import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsPowerMulUnitNorm

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `h : Rmu l ≤ (Kmu l).toSubring`. Rewrite using `[Rmu, Subring.closure_le]`. Introduce `z hz`. Conclude with `Subfield.subset_closure hz`. Conclude with `h hx`.
-/
theorem rmu_le_kmu {x : ℂ_[l]} (hx : x ∈ Rmu l) : x ∈ Kmu l := by
  have h : Rmu l ≤ (Kmu l).toSubring := by
    rw [Rmu, Subring.closure_le]
    intro z hz
    exact Subfield.subset_closure hz
  exact h hx

/- English proof (translation)
The claim follows from `(Kmu l).le_topologicalClosure hx`.
-/
theorem kmu_le_kur {x : ℂ_[l]} (hx : x ∈ Kmu l) : x ∈ MaximalUnramifiedExtension l := (Kmu l).le_topologicalClosure hx

/- English proof (translation)
Break down `Set.mem_insert_iff.mp hξ with rfl | h` into its components or cases. Conclude with `(MaximalUnramifiedExtension l).zero_mem`. Conclude with `kmu_le_kur l (Subfield.subset_closure h)`.
-/
theorem tch_mem_kur {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ξ ∈ MaximalUnramifiedExtension l := by
  rcases Set.mem_insert_iff.mp hξ with rfl | h
  · exact (MaximalUnramifiedExtension l).zero_mem
  · exact kmu_le_kur l (Subfield.subset_closure h)

/- English proof (translation)
Establish `h` using `IsUltrametricDist.dist_triangle_max x 0 y`. Rewrite `h` using `[dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg]`. Conclude with `h`.
-/
theorem norm_sub_le_max_padic (x y : ℂ_[l]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.dist_triangle_max x 0 y
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, sub_zero, zero_sub, norm_neg] at h
  exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with hlt | hgt` into its components or cases. Establish `h1` using `norm_sub_le_max_padic l x (x - y)`. Rewrite `h1` using `[sub_sub_cancel]`. Rewrite `h` using `[max_eq_right hlt.le]`.

Establish `h2 : max ‖x‖ ‖x - y‖ < ‖y‖` using `max_lt hlt h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `norm_sub_le_max_padic l y (y - x)`. Rewrite `h1` using `[sub_sub_cancel]`. Rewrite `h` using `[max_eq_left hgt.le, norm_sub_rev]`.

Establish `h2 : max ‖y‖ ‖y - x‖ < ‖x‖` using `max_lt hgt h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_eq_of_norm_sub_lt_max {x y : ℂ_[l]} (h : ‖x - y‖ < max ‖x‖ ‖y‖) : ‖x‖ = ‖y‖ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h1
    rw [max_eq_right hlt.le] at h
    have h2 : max ‖x‖ ‖x - y‖ < ‖y‖ := max_lt hlt h
    linarith
  · have h1 := norm_sub_le_max_padic l y (y - x)
    rw [sub_sub_cancel] at h1
    rw [max_eq_left hgt.le, norm_sub_rev] at h
    have h2 : max ‖y‖ ‖y - x‖ < ‖x‖ := max_lt hgt h
    linarith

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)`. Rewrite `h` using `[PadicAlgCl.norm_extends, Padic.norm_p]`. Establish `e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l])` using `by simp`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
private theorem norm_natCast_l_padicComplex_eq_inv : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends (p := l) ((l : ℚ_[l]) : PadicAlgCl l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p] at h
  have e : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [e] at h
  exact h

/- English proof (translation)
Rewrite using `[norm_natCast_l_padicComplex_eq_inv l]`. Conclude with `inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)`.
-/
theorem norm_prime_pos_complexPadic : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime l).pos)

/- English proof (translation)
Rewrite using `[norm_natCast_l_padicComplex_eq_inv l]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)`.
-/
theorem norm_prime_lt_one_complexPadic : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_natCast_l_padicComplex_eq_inv l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : Nat.Prime l).one_lt)

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0, norm_zero]`. Conclude with `norm_nonneg _`. Take `⟨m, a, -, b, -, ha, hb, rfl⟩` from `kmu_shape l hx hx0`. Establish `hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m`.

Rewrite using `[norm_mul, norm_div, ha, hb, norm_zpow]`. Simplify using the standard rewrite rules. Rewrite `h1`, the goal using `[hn]`. Establish `hm : 1 ≤ m`. Assume the negation of the conclusion as `hc`.

Establish `hm0 : m ≤ 0` using `by omega`. Use `one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem kmu_discrete {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; exact norm_nonneg _
  obtain ⟨m, a, -, b, -, ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1 ⊢
  have hm : 1 ≤ m := by
    by_contra hc
    have hm0 : m ≤ 0 := by omega
    have := one_le_zpow_of_nonpos₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm0
    linarith
  calc ‖(l : ℂ_[l])‖ ^ m ≤ ‖(l : ℂ_[l])‖ ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l).le hm
    _ = ‖(l : ℂ_[l])‖ := zpow_one _

/- English proof (translation)
Take `⟨f, hf, r, hr, h⟩` from `rmu_frob l a ha`. Use `tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_` and prove the remaining obligations. Rewrite using `[h, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)`.
-/
theorem exists_teichmuller_rep_mod_prime {a : ℂ_[l]} (ha : a ∈ Rmu l) : ∃ ξ ∈ Tch l, ‖a - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨f, hf, r, hr, h⟩ := rmu_frob l a ha
  refine tch_near l a (rmu_norm_le l ha) f hf _ (norm_prime_lt_one_complexPadic l) ?_
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

/- English proof (translation)
Break down `lt_or_eq_of_le h1 with h1 | h1` into its components or cases. Conclude with `⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩`. Establish `hx0 : x ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, norm_zero]`.

Conclude with `zero_ne_one h1`. Take `⟨m, a, ha', b, hb', ha, hb, rfl⟩` from `kmu_shape l hx hx0`. Establish `hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m`. Rewrite using `[norm_mul, norm_div, ha, hb, norm_zpow]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hn]`. Establish `hm : m = 0`. Break down `lt_trichotomy m 0 with h | h | h` into its components or cases. Use `one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h`. Use `zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Substitute `hm` using the available equality. Take `⟨α, hα, hαa⟩` from `exists_teichmuller_rep_mod_prime l ha'`.

Take `⟨β, hβ, hβb⟩` from `exists_teichmuller_rep_mod_prime l hb'`. Establish `hβ1 : ‖β‖ = 1`. Establish `h2 : ‖b - β‖ < max ‖b‖ ‖β‖` using `lt_of_le_of_lt hβb (lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) (hb ▸ le_max_left _ _))`. Rewrite using `[← norm_eq_of_norm_sub_lt_max l h2, hb]`. Establish `hb0 : b ≠ 0` using `by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb`.

Establish `hβ0 : β ≠ 0` using `by intro h; rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1`. Use `⟨α * β⁻¹, tch_mul l hα (tch_inv l hβ), ?_⟩` and prove the remaining obligations. Establish `he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹ = ((a - α) * β - α * (b - β)) / (b * β)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]`. Use `(norm_sub_le_max_padic l _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hβ1, mul_one]`. Conclude with `hαa`. Rewrite using `[norm_mul]`.

Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (tch_norm_le l hα)).trans hβb`.
-/
theorem kmu_rep {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases lt_or_eq_of_le h1 with h1 | h1
  · exact ⟨0, Set.mem_insert _ _, by rw [sub_zero]; exact kmu_discrete l hx h1⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨m, a, ha', b, hb', ha, hb, rfl⟩ := kmu_shape l hx hx0
  have hn : ‖(l : ℂ_[l]) ^ m * (a / b)‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [norm_mul, norm_div, ha, hb, norm_zpow]; simp
  rw [hn] at h1
  have hm : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · have := one_lt_zpow_of_neg₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
    · exact h
    · have := zpow_lt_one₀ (norm_prime_pos_complexPadic l) (norm_prime_lt_one_complexPadic l) h
      linarith
  subst hm
  obtain ⟨α, hα, hαa⟩ := exists_teichmuller_rep_mod_prime l ha'
  obtain ⟨β, hβ, hβb⟩ := exists_teichmuller_rep_mod_prime l hb'
  have hβ1 : ‖β‖ = 1 := by
    have h2 : ‖b - β‖ < max ‖b‖ ‖β‖ :=
      lt_of_le_of_lt hβb (lt_of_lt_of_le (norm_prime_lt_one_complexPadic l) (hb ▸ le_max_left _ _))
    rw [← norm_eq_of_norm_sub_lt_max l h2, hb]
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hβ0 : β ≠ 0 := by intro h; rw [h, norm_zero] at hβ1; exact zero_ne_one hβ1
  refine ⟨α * β⁻¹, tch_mul l hα (tch_inv l hβ), ?_⟩
  have he : (l : ℂ_[l]) ^ (0 : ℤ) * (a / b) - α * β⁻¹
      = ((a - α) * β - α * (b - β)) / (b * β) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul b, hb, hβ1, mul_one, div_one]
  refine (norm_sub_le_max_padic l _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, hβ1, mul_one]; exact hαa
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (tch_norm_le l hα)).trans hβb

/- English proof (translation)
Establish `hc : x ∈ closure ((Kmu l : Set ℂ_[l]))` using `hx`. Take `⟨y, hy, hd⟩` from `Metric.mem_closure_iff.mp hc e he`. Conclude with `⟨y, hy, by rwa [dist_eq_norm] at hd⟩`.
-/
theorem kur_approx {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (e : ℝ) (he : 0 < e) :
    ∃ y ∈ Kmu l, ‖x - y‖ < e := by
  have hc : x ∈ closure ((Kmu l : Set ℂ_[l])) := hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp hc e he
  exact ⟨y, hy, by rwa [dist_eq_norm] at hd⟩

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Rewrite using `[norm_zero]`. Conclude with `norm_nonneg _`. Establish `hpos : 0 < ‖x‖` using `norm_pos_iff.mpr hx0`. Take `⟨y, hy, hxy⟩` from `kur_approx l hx ‖x‖ hpos`.

Establish `heq : ‖x‖ = ‖y‖` using `norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))`. Rewrite `h1`, the goal using `[heq]`. Conclude with `kmu_discrete l hy h1`.
-/
theorem kur_discrete {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ < 1) : ‖x‖ ≤ ‖(l : ℂ_[l])‖ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [norm_zero]
    exact norm_nonneg _
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖x‖ hpos
  have heq : ‖x‖ = ‖y‖ := norm_eq_of_norm_sub_lt_max l (lt_of_lt_of_le hxy (le_max_left _ _))
  rw [heq] at h1 ⊢
  exact kmu_discrete l hy h1

/- English proof (translation)
Take `⟨y, hy, hxy⟩` from `kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)`. Establish `hl1` using `norm_prime_lt_one_complexPadic l`. Establish `hy1 : ‖y‖ ≤ 1`. Establish `h` using `norm_sub_le_max_padic l x (x - y)`. Rewrite `h` using `[sub_sub_cancel]`.

Conclude with `h.trans (max_le h1 (by linarith))`. Take `⟨ξ, hξ, hyξ⟩` from `kmu_rep l hy hy1`. Use `⟨ξ, hξ, ?_⟩` and prove the remaining obligations. Establish `h` using `norm_sub_le_max_padic l (x - y) (ξ - y)`. Rewrite `h` using `[sub_sub_sub_cancel_right, norm_sub_rev ξ y]`.

Conclude with `h.trans (max_le hxy.le hyξ)`.
-/
theorem kur_rep {x : ℂ_[l]} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨y, hy, hxy⟩ := kur_approx l hx ‖(l : ℂ_[l])‖ (norm_prime_pos_complexPadic l)
  have hl1 := norm_prime_lt_one_complexPadic l
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_sub_le_max_padic l x (x - y)
    rw [sub_sub_cancel] at h
    exact h.trans (max_le h1 (by linarith))
  obtain ⟨ξ, hξ, hyξ⟩ := kmu_rep l hy hy1
  refine ⟨ξ, hξ, ?_⟩
  have h := norm_sub_le_max_padic l (x - y) (ξ - y)
  rw [sub_sub_sub_cancel_right, norm_sub_rev ξ y] at h
  exact h.trans (max_le hxy.le hyξ)

end ReciprocityTheory.ChartRestriction.L1
