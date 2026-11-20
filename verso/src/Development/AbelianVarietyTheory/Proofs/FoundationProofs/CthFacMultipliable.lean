import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.CthMult

def Good (f : ℕ → ℂ) : Prop := Summable (fun m => ‖f m - 1‖)

end GlobalTheory.Sieg.CthMult

open scoped UpperHalfPlane MatrixGroups Manifold in

/- English proof (translation)
Introduce `c q t hq _`. Use `set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 / ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg`. Establish `hgd : DifferentiableAt ℂ g 0`. Apply `DifferentiableAt.div (by fun_prop) (by fun_prop)` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Establish `hg0 : g 0 = 1` using `by simp [hg]`. Establish `hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1))`. Establish `h` using `hgd.isBigO_sub`. Rewrite `h` using `[hg0]`. Simplify using `only [sub_zero] at h`.

Establish `ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0)` using `(tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)`. Conclude with `h.comp_tendsto ht`. Establish `hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖)`. Use `summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_` and prove the remaining obligations. Conclude with `(summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)`.

Simplify `hbig.norm_left.norm_right` using `[norm_pow]`. Establish `hmul` using `multipliable_one_add_of_summable hsum`. Simplify `hmul` using `[hg, _root_.GlobalTheory.Sieg.cthFac]`.
-/
theorem _root_.GlobalTheory.Sieg.cthFac_multipliable : ∀ (c : ℕ) (q t : ℂ), ‖q‖ < 1 → t ≠ 0 →
    Multipliable (fun m : ℕ => _root_.GlobalTheory.Sieg.cthFac c q t (m + 1)) := by
  intro c q t hq _
  set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 /
    ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg
  have hgd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simp
  have hg0 : g 0 = 1 := by simp [hg]
  have hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1)) := by
    have h := hgd.isBigO_sub
    rw [hg0] at h
    simp only [sub_zero] at h
    have ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    exact h.comp_tendsto ht
  have hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖) := by
    refine summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
    · simpa [norm_pow] using hbig.norm_left.norm_right
  have hmul := multipliable_one_add_of_summable hsum
  simpa [hg, _root_.GlobalTheory.Sieg.cthFac] using hmul
