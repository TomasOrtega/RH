import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open GlobalTheory.UT

namespace GlobalTheory.TestFibre

/- English proof (translation)
Introduce `F _ v X T _ χ cf ζ w α q hS hζ hχ hT hα hβ`. Assume the negation of the conclusion as `hcon`. Establish `hw : ∀ t, (q : WithTop ℚ) < v (w t)` using `fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩`. Establish `hq : (q : WithTop ℚ) ≠ ⊤` using `WithTop.coe_ne_top`. Establish `hne : ∀ t, χ t α ≠ 0` using `fun t h => by`.

Establish `h1` using `hχ t α`. Rewrite `h1` using `[h, v.map_zero]`. Conclude with `WithTop.top_ne_zero h1`. Establish `hinv : ∀ t, v (χ t α)⁻¹ = 0` using `fun t => by`. Establish `h1 : v ((χ t α)⁻¹ * χ t α) = 0` using `by rw [inv_mul_cancel₀ (hne t), v.map_one]`.

Rewrite `h1` using `[v.map_mul, hχ t α, add_zero]`. Then use the resulting hypothesis. Use `choose S hS' using fun t => hS t (q + 1)`. Use `set U : Finset X := insert α (Finset.univ.biUnion S) with hU`. Establish `hαU : α ∈ U` using `Finset.mem_insert_self _ _`. Establish `hSU : ∀ t, S t ⊆ U` using `fun t x hx => Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, hx⟩)`.

Establish `hq1 : (q : WithTop ℚ) < ((q + 1 : ℚ) : WithTop ℚ)` using `WithTop.coe_lt_coe.2 (by linarith)`. Establish `hA : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t))` using `v.map_lt_sum hq fun t _ => by`. Rewrite using `[v.map_mul, v.map_mul, hinv, hζ, zero_add, zero_add]`. Conclude with `hw t`. Establish `hB : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β))` using `v.map_lt_sum hq fun t _ => by`.

Rewrite using `[v.map_mul, hinv, zero_add]`. Conclude with `hq1.trans_le (hS' t U (hSU t))`. Establish `hC : (q : WithTop ℚ) < v (∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β)` using `v.map_lt_sum hq fun β hb => by`. Break down `hβ β (Finset.ne_of_mem_erase hb) with h | h` into its components or cases. Rewrite using `[h, zero_mul, v.map_zero]`.

Conclude with `WithTop.coe_lt_top q`. Rewrite using `[v.map_mul]`. Establish `h0 : (0 : WithTop ℚ) ≤ v (∑ t, (χ t α)⁻¹ * χ t β)` using `v.map_le_sum fun t _ => by rw [v.map_mul, hinv, hχ, add_zero]`. Conclude with `h.trans_le (le_add_of_nonneg_left h0)`. Establish `e1 : ∑ t, (χ t α)⁻¹ * χ t α = ((Fintype.card T : ℕ) : F)`.

Rewrite using `[Finset.sum_congr rfl fun t _ => inv_mul_cancel₀ (hne t)]`. Simplify using the standard rewrite rules. Establish `e2 : ∑ t, (χ t α)⁻¹ * (∑ β ∈ U, χ t β * cf β) = ∑ β ∈ U, (∑ t, (χ t α)⁻¹ * χ t β) * cf β`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.

Establish `e : ((Fintype.card T : ℕ) : F) * cf α = (∑ t, (χ t α)⁻¹ * (ζ t * w t)) + (-(∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) + -(∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β))`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[e2, ← Finset.add_sum_erase U _ hαU, e1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : (q : WithTop ℚ) < v (((Fintype.card T : ℕ) : F) * cf α)`.

Rewrite using `[e]`. Conclude with `v.map_lt_add hA (v.map_lt_add (by rwa [v.map_neg]) (by rwa [v.map_neg]))`. Rewrite `hfin` using `[v.map_mul, hT, zero_add, hα]`. Conclude with `lt_irrefl _ hfin`.
-/
theorem exists_val_le_of_sumV_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  classical
  intro F _ v X T _ χ cf ζ w α q hS hζ hχ hT hα hβ
  by_contra hcon
  have hw : ∀ t, (q : WithTop ℚ) < v (w t) := fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩
  have hq : (q : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
  have hne : ∀ t, χ t α ≠ 0 := fun t h => by
    have h1 := hχ t α
    rw [h, v.map_zero] at h1
    exact WithTop.top_ne_zero h1
  have hinv : ∀ t, v (χ t α)⁻¹ = 0 := fun t => by
    have h1 : v ((χ t α)⁻¹ * χ t α) = 0 := by rw [inv_mul_cancel₀ (hne t), v.map_one]
    rwa [v.map_mul, hχ t α, add_zero] at h1
  choose S hS' using fun t => hS t (q + 1)
  set U : Finset X := insert α (Finset.univ.biUnion S) with hU
  have hαU : α ∈ U := Finset.mem_insert_self _ _
  have hSU : ∀ t, S t ⊆ U := fun t x hx =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, hx⟩)
  have hq1 : (q : WithTop ℚ) < ((q + 1 : ℚ) : WithTop ℚ) := WithTop.coe_lt_coe.2 (by linarith)
  have hA : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, v.map_mul, hinv, hζ, zero_add, zero_add]; exact hw t
  have hB : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, hinv, zero_add]; exact hq1.trans_le (hS' t U (hSU t))
  have hC : (q : WithTop ℚ) < v (∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β) :=
    v.map_lt_sum hq fun β hb => by
      rcases hβ β (Finset.ne_of_mem_erase hb) with h | h
      · rw [h, zero_mul, v.map_zero]; exact WithTop.coe_lt_top q
      · rw [v.map_mul]
        have h0 : (0 : WithTop ℚ) ≤ v (∑ t, (χ t α)⁻¹ * χ t β) :=
          v.map_le_sum fun t _ => by rw [v.map_mul, hinv, hχ, add_zero]
        exact h.trans_le (le_add_of_nonneg_left h0)
  have e1 : ∑ t, (χ t α)⁻¹ * χ t α = ((Fintype.card T : ℕ) : F) := by
    rw [Finset.sum_congr rfl fun t _ => inv_mul_cancel₀ (hne t)]
    simp
  have e2 : ∑ t, (χ t α)⁻¹ * (∑ β ∈ U, χ t β * cf β) = ∑ β ∈ U, (∑ t, (χ t α)⁻¹ * χ t β) * cf β := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have e : ((Fintype.card T : ℕ) : F) * cf α =
      (∑ t, (χ t α)⁻¹ * (ζ t * w t)) +
        (-(∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) +
          -(∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e2, ← Finset.add_sum_erase U _ hαU, e1]
    ring
  have hfin : (q : WithTop ℚ) < v (((Fintype.card T : ℕ) : F) * cf α) := by
    rw [e]
    exact v.map_lt_add hA (v.map_lt_add (by rwa [v.map_neg]) (by rwa [v.map_neg]))
  rw [v.map_mul, hT, zero_add, hα] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.TestFibre
