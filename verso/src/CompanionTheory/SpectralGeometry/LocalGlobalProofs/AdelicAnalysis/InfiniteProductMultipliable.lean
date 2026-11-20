import Mathlib

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AbsTprod

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem multipliable_of_summable_abs_sub_one {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hm := multipliable_one_add_of_summable h'
  have hfun : (fun v => 1 + (a v - 1)) = a := funext fun v => by ring
  rwa [hfun] at hm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tprod_nonneg_of_nonneg {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by
  exact tprod_nonneg h0

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem tprod_ne_zero_of_summable {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hne : ∀ v, 1 + (a v - 1) ≠ 0 := fun v => by simpa using h0 v
  have hp := tprod_one_add_ne_zero_of_summable (f := fun v => a v - 1) hne h'
  simpa using hp

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem tprod_eq_prod_mul_tprod_compl {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by
  have hsub : ∀ p : ι → Prop, Multipliable (fun v : {v // p v} => a v.1) := fun p =>
    GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one (a := fun v : {v // p v} => a v.1)
      (h.comp_injective Subtype.val_injective)
  refine ⟨hsub _, ?_⟩
  have key := Multipliable.tprod_mul_tprod_compl (f := a) (s := (S : Set ι))
    (hsub (· ∈ (S : Set ι))) (hsub (· ∈ (S : Set ι)ᶜ))
  rw [← key, Finset.tprod_subtype']
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem abs_tprod : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  intro ι a h
  have hm := GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one h
  refine ⟨hm, fun S => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl h S, fun hpos => ?_,
    fun h0 => GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm h0⟩
  exact lt_of_le_of_ne (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg hm fun v => (hpos v).le)
    (GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable h fun v => (hpos v).ne').symm

end GlobalTheory.CompanionTheory.SW.AbsTprod
