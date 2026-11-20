import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `G _ _ p _ χ hχ hadd g₀ hg₀`. Establish `hex : ∃ n : ℕ, ∃ g, χ g ≠ 0 ∧ (χ g).valuation = n` using `⟨_, g₀, hg₀, rfl⟩`. Take `⟨g₁, hg₁, hv₁⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ g, χ g ≠ 0 → (χ g₁).valuation ≤ (χ g).valuation`. Introduce `g hg`.

Rewrite using `[hv₁]`. Conclude with `Nat.find_min' hex ⟨g, hg, rfl⟩`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt.le`. Establish `hle : ∀ g, ‖χ g‖ ≤ ‖χ g₁‖`. Introduce `g`.

Distinguish the cases in `hg : χ g = 0`. Rewrite using `[hg, norm_zero]`. Conclude with `norm_nonneg _`. Rewrite using `[PadicInt.norm_eq_zpow_neg_valuation hg, PadicInt.norm_eq_zpow_neg_valuation hg₁]`. Apply `zpow_le_zpow_right₀ hp1` to reduce the goal to its premises.

Use `hmin g hg` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hn₁ : (χ g₁ : ℚ_[p]) ≠ 0` using `fun h => hg₁ (PadicInt.coe_eq_zero.1 h)`. Establish `hbd : ∀ g, ‖(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p])‖ ≤ 1`. Introduce `g`.

Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hn₁)]`. Conclude with `hle g`. Use `⟨fun g => ⟨(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]), hbd g⟩, ?_, ?_, ?_, g₁, ?_⟩` and prove the remaining obligations. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `(continuous_subtype_val.comp hχ).div_const _`.

Introduce `g h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((χ (g * h) : ℚ_[p])) / (χ g₁ : ℚ_[p]) = (χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]) + (χ h : ℚ_[p]) / (χ g₁ : ℚ_[p])`. Rewrite using `[hadd, PadicInt.coe_add, add_div]`. Introduce `g hg`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hg]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[div_self hn₁]`.
-/
theorem padicInt_hom_normalize : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  intro G _ _ p _ χ hχ hadd g₀ hg₀
  classical
  have hex : ∃ n : ℕ, ∃ g, χ g ≠ 0 ∧ (χ g).valuation = n := ⟨_, g₀, hg₀, rfl⟩
  obtain ⟨g₁, hg₁, hv₁⟩ := Nat.find_spec hex
  have hmin : ∀ g, χ g ≠ 0 → (χ g₁).valuation ≤ (χ g).valuation := by
    intro g hg
    rw [hv₁]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hle : ∀ g, ‖χ g‖ ≤ ‖χ g₁‖ := by
    intro g
    by_cases hg : χ g = 0
    · rw [hg, norm_zero]; exact norm_nonneg _
    rw [PadicInt.norm_eq_zpow_neg_valuation hg, PadicInt.norm_eq_zpow_neg_valuation hg₁]
    apply zpow_le_zpow_right₀ hp1
    have := hmin g hg
    omega
  have hn₁ : (χ g₁ : ℚ_[p]) ≠ 0 := fun h => hg₁ (PadicInt.coe_eq_zero.1 h)
  have hbd : ∀ g, ‖(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p])‖ ≤ 1 := by
    intro g
    rw [norm_div, div_le_one (norm_pos_iff.2 hn₁)]
    exact hle g
  refine ⟨fun g => ⟨(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]), hbd g⟩, ?_, ?_, ?_, g₁, ?_⟩
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp hχ).div_const _
  · intro g h
    apply Subtype.ext
    show ((χ (g * h) : ℚ_[p])) / (χ g₁ : ℚ_[p]) = (χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]) + (χ h : ℚ_[p]) / (χ g₁ : ℚ_[p])
    rw [hadd, PadicInt.coe_add, add_div]
  · intro g hg
    apply Subtype.ext
    simp [hg]
  · apply Subtype.ext
    simp [div_self hn₁]

end GlobalTheory
