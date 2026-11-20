import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.InHCorner
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

def ballLe (r : ValueGroupWithZero k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ r}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact ((valuation k).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

def ballLt (γ : (ValueGroupWithZero k)ˣ) : AddSubgroup k where
  carrier := {x | valuation k x < γ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (valuation k).map_add_lt ha hb
  zero_mem' := by simp [Units.zero_lt]
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

/- English proof (translation)
The claim follows from `(ballLt γ).isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ hx => hx⟩)`.
-/
theorem isOpen_ballLt (γ : (ValueGroupWithZero k)ˣ) : IsOpen ((ballLt γ : AddSubgroup k) : Set k) :=
  (ballLt γ).isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ hx => hx⟩)

/- English proof (translation)
Establish `hU : {t : k | ‖((ψ t : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k)`. Establish `hc : Continuous fun t : k => ‖((ψ t : Circle) : ℂ) - 1‖` using `((continuous_subtype_val.comp hψ).sub continuous_const).norm`. Conclude with `(isOpen_lt hc continuous_const).mem_nhds (by simp)`. Take `⟨γ, hγ⟩` from `(IsValuativeTopology.mem_nhds_zero_iff _).1 hU`. Set `H : Subgroup Circle` to `{ carrier := ψ '' {x | valuation k x < γ} mul_mem' := by`.

Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`. Conclude with `⟨a + b, (valuation k).map_add_lt ha hb, AddChar.map_add_eq_mul ψ a b⟩`. Use the proof step `one_mem' := ⟨0, by simp [Units.zero_lt], AddChar.map_zero_eq_one ψ⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Conclude with `⟨-a, by simpa [Valuation.map_neg] using ha, AddChar.map_neg_eq_inv ψ a⟩ }`. Establish `hH` using `GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H (by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `hγ ha)`. Use `⟨γ, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `: ψ x ∈ H` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[hH]`. Conclude with `Subgroup.mem_bot.1 this`.
-/
theorem psi_ball (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ x : k, valuation k x < γ → ψ x = 1 := by
  have hU : {t : k | ‖((ψ t : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    have hc : Continuous fun t : k => ‖((ψ t : Circle) : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hU
  let H : Subgroup Circle :=
    { carrier := ψ '' {x | valuation k x < γ}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, (valuation k).map_add_lt ha hb, AddChar.map_add_eq_mul ψ a b⟩
      one_mem' := ⟨0, by simp [Units.zero_lt], AddChar.map_zero_eq_one ψ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, by simpa [Valuation.map_neg] using ha, AddChar.map_neg_eq_inv ψ a⟩ }
  have hH := GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H (by
    rintro _ ⟨a, ha, rfl⟩; exact hγ ha)
  refine ⟨γ, fun x hx => ?_⟩
  have : ψ x ∈ H := ⟨x, hx, rfl⟩
  rw [hH] at this
  exact Subgroup.mem_bot.1 this

/- English proof (translation)
Assume the negation of the conclusion as `hb'`. Establish `hb` using `not_lt.1 hb'`. Establish `hb0 : (0 : ValueGroupWithZero k) < valuation k b` using `lt_of_lt_of_le (Units.zero_lt γ) hb`. Establish `hb0' : b ≠ 0` using `fun h0 => by simp [h0] at hb0`. Apply `hy` to reduce the goal to its premises.

Establish `e : b * (y / b) = y` using `by field_simp`. Rewrite using `[← e]`. Use `h _ ?_` and prove the remaining obligations. Rewrite using `[map_div₀, div_eq_mul_inv, Units.val_inv_eq_inv_val]`. Use `gcongr (valuation k y) * ?_`.

Conclude with `(inv_le_inv₀ hb0 (Units.zero_lt γ)).2 hb`.
-/
theorem small_of_triv (ψ : AddChar k Circle) (y : k) (hy : ψ y ≠ 1) (γ : (ValueGroupWithZero k)ˣ) (b : k)
    (h : ∀ t : k, valuation k t ≤ valuation k y * ↑γ⁻¹ → ψ (b * t) = 1) : valuation k b < γ := by
  by_contra hb'
  have hb := not_lt.1 hb'
  have hb0 : (0 : ValueGroupWithZero k) < valuation k b := lt_of_lt_of_le (Units.zero_lt γ) hb
  have hb0' : b ≠ 0 := fun h0 => by simp [h0] at hb0
  apply hy
  have e : b * (y / b) = y := by field_simp
  rw [← e]
  refine h _ ?_
  rw [map_div₀, div_eq_mul_inv, Units.val_inv_eq_inv_val]
  gcongr (valuation k y) * ?_
  exact (inv_le_inv₀ hb0 (Units.zero_lt γ)).2 hb

/- English proof (translation)
Establish `hc : ∀ x' : (Fin (m + 1) → k) → (Fin (m + 1) → k), Continuous x' → Continuous fun x => colM c (x' x)`. Introduce `x' hx'`. Use `continuous_const.add (continuous_matrix fun p q => ?_)` and prove the remaining obligations. Distinguish the cases in `h : q = c ∧ p < c`. Simplify using `only [Matrix.of_apply, if_pos h]`.

Conclude with `(continuous_apply p).comp hx'`. Simplify using `only [Matrix.of_apply, if_neg h]`. Conclude with `continuous_const`. Conclude with `Units.continuous_iff.2 ⟨hc id continuous_id, hc (fun x => -x) continuous_neg⟩`.
-/
theorem continuous_U (c : Fin (m + 1)) : Continuous (fun x : Fin (m + 1) → k => U c x) := by
  have hc : ∀ x' : (Fin (m + 1) → k) → (Fin (m + 1) → k), Continuous x' →
      Continuous fun x => colM c (x' x) := by
    intro x' hx'
    refine continuous_const.add (continuous_matrix fun p q => ?_)
    by_cases h : q = c ∧ p < c
    · simp only [Matrix.of_apply, if_pos h]; exact (continuous_apply p).comp hx'
    · simp only [Matrix.of_apply, if_neg h]; exact continuous_const
  exact Units.continuous_iff.2 ⟨hc id continuous_id, hc (fun x => -x) continuous_neg⟩

end DiscreteGroups.sglob.LConvKir
