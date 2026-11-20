import Formalism.EllipticTorsion.Statement

universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

/- English proof (translation)
Establish `h2 : ‖(2 : K)‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_natCast_le_one K 2`. Establish `h3 : ‖(3 : K)‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_natCast_le_one K 3`. Establish `h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖`.

Establish `: (1 : K) = 3 + -2` using `by norm_num`. Rewrite using `[this]`. Simplify `IsUltrametricDist.norm_add_le_max (3 : K) (-2)` using `[norm_neg]`. Rewrite `h1` using `[norm_one]`. Distinguish the cases in `h : ‖(2 : K)‖ = 1`.

Conclude with `Or.inl h`. Use `right`. Establish `hlt : ‖(2 : K)‖ < 1` using `lt_of_le_of_ne h2 h`. Break down `le_max_iff.mp h1 with h' | h'` into its components or cases. Conclude with `le_antisymm h3 h'`.

Conclude with `absurd h' (not_le.mpr hlt)`.
-/
lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

/- English proof (translation)
Establish `hne : W.Δ ≠ 0`. Introduce `h`. Rewrite `hΔ` using `[h, norm_zero]`. Conclude with `zero_ne_one hΔ`. Establish `: W.IsElliptic` using `⟨hne.isUnit⟩`.

Use `⟨W, inferInstance, hI, hΔ, ?_⟩` and prove the remaining obligations. Rewrite using `[WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']`. Clear the denominators using the available nonvanishing facts.
-/
lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt

namespace Formalism.ELL

open Formalism.ELL.unitAtAlt

/- English proof (translation)
Introduce `K _ _ _ j hj`. Break down `two_or_three (K := K) with h2 | h3` into its components or cases. Take `⟨l, hl, _hl1, hc, hΔ⟩` from `hL K h2 j hj`. Use `of_model (legendre l) j ?_ hc hΔ` and prove the remaining obligations. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]`.

Simplify using the standard rewrite rules. Rewrite using `[norm_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans ?_` and prove the remaining obligations. Simplify using `[hl]`. Simplify using the standard rewrite rules.

Conclude with `hl.le`. Simplify using the standard rewrite rules. Take `⟨a, ha, hc, hΔ⟩` from `hD K h3 j hj`. Use `of_model (deuring a) j ?_ hc hΔ` and prove the remaining obligations. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]`.

Conclude with `ha`. Apply the tactic sequence `all_goals simp`.
-/
theorem modelUnit_of (hL : Formalism.ELL.ModelLegendre.{u}) (hD : Formalism.ELL.ModelDeuring.{u}) :
    Formalism.ELL.ModelUnit.{u} := by
  intro K _ _ _ j hj
  rcases two_or_three (K := K) with h2 | h3
  · obtain ⟨l, hl, _hl1, hc, hΔ⟩ := hL K h2 j hj
    refine of_model (legendre l) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]
    · simp
    · rw [norm_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hl]
    · simp
    · exact hl.le
    · simp
  · obtain ⟨a, ha, hc, hΔ⟩ := hD K h3 j hj
    refine of_model (deuring a) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]
    · exact ha
    all_goals simp

end Formalism.ELL
