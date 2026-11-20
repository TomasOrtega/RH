import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

/- English proof (translation)
Establish `hπ : (0 : ValueGroupWithZero k) < uniformizer k` using `uniformizer_pos`. Establish `hr' : 0 < valuation k r` using `zero_lt_iff.2 (by simpa using hr)`. Establish `hex : ∃ n : ℕ, ∃ x, valuation k x * uniformizer k ^ n ≤ valuation k r ∧ f x ≠ f 0`. Establish `hy0 : 0 < valuation k y` using `zero_lt_iff.2 (by rintro h0; rw [map_eq_zero] at h0; exact hy (by rw [h0]))`. Take `⟨n, hn⟩` from `exists_pow_lt₀ (uniformizer_lt_one (R := k)) (Units.mk0 (valuation k r / valuation k y) (div_pos hr' hy0).ne')`.

Use `⟨n, y, ?_, hy⟩` and prove the remaining obligations. Rewrite `hn` using `[Units.val_mk0, lt_div_iff₀ hy0, mul_comm]`. Conclude with `hn.le`. Take `⟨b, hb, hb'⟩` from `Nat.find_spec hex`. Use `⟨b, hb', fun x hx => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Break down `hm : Nat.find hex with _ | m` into its components or cases. Rewrite `hb` using `[hm, pow_zero, mul_one]`. Conclude with `hb' (h b hb)`. Use `Nat.find_min hex (m := m) (by omega) ⟨x, ?_, hne⟩` and prove the remaining obligations.

Rewrite `hb` using `[hm]`. Establish `hb0 : 0 < valuation k b` using `zero_le'.trans_lt hx`. Establish `h1 : valuation k x / valuation k b ≤ uniformizer k` using `le_uniformizer_iff.2 ((div_lt_one₀ hb0).2 hx)`. Rewrite `h1` using `[div_le_iff₀ hb0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_jump_point {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (f : k → ℂ) {r : k} (hr : r ≠ 0) (h : ∀ x, valuation k x ≤ valuation k r → f x = f 0) {y : k} (hy : f y ≠ f 0) :
    ∃ b : k, f b ≠ f 0 ∧ ∀ x, valuation k x < valuation k b → f x = f 0 := by
  classical
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hr' : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  have hex : ∃ n : ℕ, ∃ x, valuation k x * uniformizer k ^ n ≤ valuation k r ∧ f x ≠ f 0 := by
    have hy0 : 0 < valuation k y := zero_lt_iff.2 (by rintro h0; rw [map_eq_zero] at h0; exact hy (by rw [h0]))
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k))
      (Units.mk0 (valuation k r / valuation k y) (div_pos hr' hy0).ne')
    refine ⟨n, y, ?_, hy⟩
    rw [Units.val_mk0, lt_div_iff₀ hy0, mul_comm] at hn
    exact hn.le
  obtain ⟨b, hb, hb'⟩ := Nat.find_spec hex
  refine ⟨b, hb', fun x hx => ?_⟩
  by_contra hne
  rcases hm : Nat.find hex with _ | m
  · rw [hm, pow_zero, mul_one] at hb
    exact hb' (h b hb)
  · refine Nat.find_min hex (m := m) (by omega) ⟨x, ?_, hne⟩
    rw [hm] at hb
    have hb0 : 0 < valuation k b := zero_le'.trans_lt hx
    have h1 : valuation k x / valuation k b ≤ uniformizer k := le_uniformizer_iff.2 ((div_lt_one₀ hb0).2 hx)
    rw [div_le_iff₀ hb0] at h1
    calc valuation k x * uniformizer k ^ m ≤ uniformizer k * valuation k b * uniformizer k ^ m := by gcongr
      _ = valuation k b * uniformizer k ^ (m + 1) := by rw [pow_succ]; ac_rfl
      _ ≤ _ := hb

/- English proof (translation)
Take `⟨r, hr, h0⟩` from `h0`. Take `⟨R, hi⟩` from `hi`. Establish `hπ : (0 : ValueGroupWithZero k) < uniformizer k` using `uniformizer_pos`. Establish `hy : ∃ y : k, valuation k R < valuation k y`. Distinguish the cases in `hR : R = 0`.

Conclude with `⟨1, by simp [hR]⟩`. Establish `hR' : 0 < valuation k R` using `zero_lt_iff.2 (by simpa using hR)`. Use `⟨R / ϖ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hϖ, lt_div_iff₀ hπ]`. Conclude with `mul_lt_of_lt_one_right hR' uniformizer_lt_one`.

Take `⟨y, hy⟩` from `hy`. Take `⟨b, hb, hb'⟩` from `exists_jump_point (fun x : k => F x) hr h0 (y := y) (by show F y ≠ F (0 : k)`. Rewrite using `[hi y hy]`. Conclude with `hne.symm)`. Establish `hb0 : b ≠ 0` using `by rintro rfl; exact hb rfl`.

Establish `hvb : 0 < valuation k b` using `zero_lt_iff.2 (by simpa using hb0)`. Set `g : k → ℂ` to `fun x => F ((b * x : k) : OnePoint k)`. Establish `g1 : ∀ x, valuation k x < 1 → g x = F (0 : k)` using `fun x hx => hb' _ (by`. Rewrite using `[map_mul]`. Conclude with `mul_lt_of_lt_one_right hvb hx)`.

Establish `g2 : ∀ x, valuation k x = 1 → g x = F b` using `fun x hx => by show F ((b * x : k) : OnePoint k) = _`. Rewrite using `[mul_comm]`. Conclude with `hrad x b hx`. Establish `g3 : ∀ x z, x ≠ 0 → valuation k z = valuation k x → g z = g x` using `fun x z hx hz => by`. Establish `hvx : valuation k x ≠ 0` using `by simpa using hx`.

Use `hrad (z / x) (b * x) (by rw [map_div₀, hz, div_self hvx])` as an intermediate fact. Use `show F ((b * z : k) : OnePoint k) = F ((b * x : k) : OnePoint k)`. Rewrite using `[← this]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Establish `hG : (fun x : OnePoint k => x.elim (F ∞) g) ∈ S` using `hS.1 F hF b 0 hb0 _ rfl fun x => by rw [add_zero]; rfl`. Establish `hG' : (fun x : OnePoint k => x.elim (F ∞) fun x => g (x - 1)) ∈ S` using `hS.1 F hF b (-b) hb0 _ rfl fun x => by show F ((b * (x - 1) : k) : OnePoint k) = _`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : F (0 : k) - F b ≠ 0` using `sub_ne_zero.2 hb.symm`.

Rewrite using `[← S.smul_mem_iff hc]`. Use `S.sub_mem hG hG' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => simp`.

Consider the case `coe x => show (F (0 : k) - F b) * (ballFn 0 ϖ x - ballFn 1 ϖ x) = g x - g (x - 1)`. Rewrite using `[ballFn_coe, ballFn_coe, hϖ, sub_zero]`. Simplify using `only [le_uniformizer_iff]`. Distinguish the cases in `h1 : valuation k x < 1`. Establish `h2 : valuation k (x - 1) = 1`.

Rewrite using `[Valuation.map_sub_swap]`. Conclude with `(valuation k).map_one_sub_of_lt h1`. Rewrite using `[if_pos h1, if_neg (by rw [h2]; exact lt_irrefl _), g1 x h1, g2 _ h2]; ring`. Distinguish the cases in `h2 : valuation k (x - 1) < 1`. Establish `h3 : valuation k x = 1`.

Use `(valuation k).map_one_add_of_lt h2` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Rewrite using `[if_neg h1, if_pos h2, g1 _ h2, g2 _ h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact h1 (by simp)`.

Establish `h3 : valuation k (x - 1) = valuation k x`. Break down `(not_lt.1 h1).eq_or_lt with h4 | h4` into its components or cases. Use `le_antisymm ?_ (h4 ▸ not_lt.1 h2)` and prove the remaining obligations. Conclude with `(valuation k).map_sub_le le_rfl (by rw [map_one]; exact h4.le)`. Conclude with `(valuation k).map_sub_eq_of_lt_left (by rwa [map_one])`.

Rewrite using `[if_neg h1, if_neg h2, g3 x _ hx0 h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ballFn_sub_mem_of_radial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (F : OnePoint k → ℂ) (hF : F ∈ S)
    (hrad : ∀ u x : k, valuation k u = 1 → F ((u * x : k) : OnePoint k) = F (x : OnePoint k))
    (h0 : ∃ r : k, r ≠ 0 ∧ ∀ x : k, valuation k x ≤ valuation k r → F (x : OnePoint k) = F ((0 : k) : OnePoint k))
    (hi : ∃ R : k, ∀ x : k, valuation k R < valuation k x → F (x : OnePoint k) = F ∞)
    (hne : F ((0 : k) : OnePoint k) ≠ F ∞) (ϖ : k) (hϖ : valuation k ϖ = uniformizer k) :
    ballFn 0 ϖ - ballFn 1 ϖ ∈ S := by
  classical
  obtain ⟨r, hr, h0⟩ := h0
  obtain ⟨R, hi⟩ := hi
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hy : ∃ y : k, valuation k R < valuation k y := by
    by_cases hR : R = 0
    · exact ⟨1, by simp [hR]⟩
    · have hR' : 0 < valuation k R := zero_lt_iff.2 (by simpa using hR)
      refine ⟨R / ϖ, ?_⟩
      rw [map_div₀, hϖ, lt_div_iff₀ hπ]
      exact mul_lt_of_lt_one_right hR' uniformizer_lt_one
  obtain ⟨y, hy⟩ := hy
  obtain ⟨b, hb, hb'⟩ := exists_jump_point (fun x : k => F x) hr h0 (y := y) (by
    show F y ≠ F (0 : k)
    rw [hi y hy]; exact hne.symm)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
  have hvb : 0 < valuation k b := zero_lt_iff.2 (by simpa using hb0)
  let g : k → ℂ := fun x => F ((b * x : k) : OnePoint k)
  have g1 : ∀ x, valuation k x < 1 → g x = F (0 : k) := fun x hx => hb' _ (by
    rw [map_mul]; exact mul_lt_of_lt_one_right hvb hx)
  have g2 : ∀ x, valuation k x = 1 → g x = F b := fun x hx => by
    show F ((b * x : k) : OnePoint k) = _
    rw [mul_comm]; exact hrad x b hx
  have g3 : ∀ x z, x ≠ 0 → valuation k z = valuation k x → g z = g x := fun x z hx hz => by
    have hvx : valuation k x ≠ 0 := by simpa using hx
    have := hrad (z / x) (b * x) (by rw [map_div₀, hz, div_self hvx])
    show F ((b * z : k) : OnePoint k) = F ((b * x : k) : OnePoint k)
    rw [← this]; congr 2; field_simp
  have hG : (fun x : OnePoint k => x.elim (F ∞) g) ∈ S :=
    hS.1 F hF b 0 hb0 _ rfl fun x => by rw [add_zero]; rfl
  have hG' : (fun x : OnePoint k => x.elim (F ∞) fun x => g (x - 1)) ∈ S :=
    hS.1 F hF b (-b) hb0 _ rfl fun x => by
      show F ((b * (x - 1) : k) : OnePoint k) = _
      congr 2; ring
  have hc : F (0 : k) - F b ≠ 0 := sub_ne_zero.2 hb.symm
  rw [← S.smul_mem_iff hc]
  convert S.sub_mem hG hG' using 1
  funext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe x =>
    show (F (0 : k) - F b) * (ballFn 0 ϖ x - ballFn 1 ϖ x) = g x - g (x - 1)
    rw [ballFn_coe, ballFn_coe, hϖ, sub_zero]
    simp only [le_uniformizer_iff]
    by_cases h1 : valuation k x < 1
    · have h2 : valuation k (x - 1) = 1 := by
        rw [Valuation.map_sub_swap]; exact (valuation k).map_one_sub_of_lt h1
      rw [if_pos h1, if_neg (by rw [h2]; exact lt_irrefl _), g1 x h1, g2 _ h2]; ring
    · by_cases h2 : valuation k (x - 1) < 1
      · have h3 : valuation k x = 1 := by
          have := (valuation k).map_one_add_of_lt h2
          rwa [add_sub_cancel] at this
        rw [if_neg h1, if_pos h2, g1 _ h2, g2 _ h3]; ring
      · have hx0 : x ≠ 0 := by rintro rfl; exact h1 (by simp)
        have h3 : valuation k (x - 1) = valuation k x := by
          rcases (not_lt.1 h1).eq_or_lt with h4 | h4
          · refine le_antisymm ?_ (h4 ▸ not_lt.1 h2)
            exact (valuation k).map_sub_le le_rfl (by rw [map_one]; exact h4.le)
          · exact (valuation k).map_sub_eq_of_lt_left (by rwa [map_one])
        rw [if_neg h1, if_neg h2, g3 x _ hx0 h3]; ring

end GlobalTheory.LocGL.ProjLine
