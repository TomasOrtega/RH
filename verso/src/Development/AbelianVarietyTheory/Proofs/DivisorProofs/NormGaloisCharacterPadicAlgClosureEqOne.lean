import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.ExpFrame.CharUnit

open NumberField Polynomial in
/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
private theorem le_one_of_forall_pow_le {a C : ℝ} (h : ∀ n : ℕ, a ^ n ≤ C) : a ≤ 1 := by
  by_contra ha
  push_neg at ha
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ha
  exact absurd (h n) (not_le.mpr hn)

open NumberField Polynomial in

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [NormedField K] (χ : Γ →* Kˣ) (hc : Continuous fun g => ((χ g : Kˣ) : K)) (g : Γ) :
    ‖((χ g : Kˣ) : K)‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hb : ∀ h : Γ, ∀ n : ℕ, ‖((χ h : Kˣ) : K)‖ ^ n ≤ C := fun h n => by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact hC _ ⟨h ^ n, rfl⟩
  have h1 := le_one_of_forall_pow_le (hb g)
  have h2 := le_one_of_forall_pow_le (hb g⁻¹)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ g : Kˣ) : K)‖ := norm_pos_iff.mpr (χ g).ne_zero
  have : 1 ≤ ‖((χ g : Kˣ) : K)‖ := by
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  linarith

open NumberField Polynomial in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (PadicAlgCl l)ˣ), Continuous (_root_.GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ χ hχ g
  refine _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact χ ?_ g
  have h := (Units.continuous_val.comp hχ).matrix_elem 0 0
  convert h using 1
  funext x
  simp [_root_.GlobalTheory.TripleGal.rk1]

end GlobalTheory.ExpFrame.CharUnit
