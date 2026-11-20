import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FNExpJ

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Rewrite using `[HahnSeries.ofPowerSeries_apply]`. Apply `HahnSeries.embDomain_notin_image_support` to reduce the goal to its premises. Introduce and unpack `⟨n, -, hn⟩`. Conclude with `hr n (by simpa using hn)`.
-/
theorem ofPowerSeries_coeff_of_ne (P : PowerSeries Ω) {r : ℚ} (hr : ∀ n : ℕ, (n : ℚ) ≠ r) :
    (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  exact hr n (by simpa using hn)

/- English proof (translation)
Introduce `Ω _ ε`. Take `⟨c, hc⟩` from `GlobalTheory.exists_hasSum_modularJ_sub_inv`. Use `set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef`. Establish `hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω)` using `fun n => by`. Rewrite using `[HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]`.

Establish `h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0` using `fun r hr => ofPowerSeries_coeff_of_ne P hr`. Establish `hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r` using `fun r hr n hn => by`. Establish `: (0 : ℚ) ≤ n` using `n.cast_nonneg`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P, ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `⟨1, one_pos, fun r hr => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : r = -1`. Conclude with `⟨-1, by simp [h1]⟩`. Distinguish the cases in `h2 : ∃ n : ℕ, (n : ℚ) = r`. Take `⟨n, rfl⟩` from `h2`.

Conclude with `⟨n, by simp⟩`. Use `push_neg at h2`. It suffices to derive a contradiction. Apply `hr` to reduce the goal to its premises. Rewrite using `[HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]`.

Introduce `z hz set τ : ℍ := ⟨z, hz⟩ with hτ`. Establish `hup : up jT z = GlobalTheory.modularJ τ`. Simplify using `only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]`. Both sides reduce to the same expression. Establish `hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z)`.

Simplify using `[Function.Periodic.qParam, hτ]`. Establish `H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹`. Use `hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by` as an intermediate fact. Simplify using `[HahnSeries.coeff_single_of_ne hr])`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹)`.

Use `(Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective (fun r hr => ?_)).mp ?_` and prove the remaining obligations. Rewrite using `[h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]`. Use `hc τ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Simplify using `only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]`.

Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `H1.add H2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `r`.

Rewrite using `[HahnSeries.coeff_add, map_add, add_mul]`. Rewrite using `[hup]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]`. Introduce `r hr`.

Rewrite using `[HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)), add_zero]`. Introduce `r`. Distinguish the cases in `h1 : r = -1`. Substitute `h1` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations.

Rewrite using `[HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]`. Simplify using the standard rewrite rules. Distinguish the cases in `h2 : ∃ n : ℕ, (n : ℚ) = r`. Take `⟨n, rfl⟩` from `h2`. Use `⟨c n, ?_⟩` and prove the remaining obligations.

Rewrite using `[HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]`. Use `push_neg at h2`. Conclude with `⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩`.
-/
theorem expansion_j : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω,
    IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧
      ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  obtain ⟨c, hc⟩ := GlobalTheory.exists_hasSum_modularJ_sub_inv
  set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef
  have hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω) := fun n => by
    rw [HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]
  have h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 :=
    fun r hr => ofPowerSeries_coeff_of_ne P hr
  have hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r := fun r hr n hn => by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  refine ⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P,
    ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun r hr => ?_⟩
    by_cases h1 : r = -1
    · exact ⟨-1, by simp [h1]⟩
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      exact ⟨n, by simp⟩
    · push_neg at h2
      exfalso
      apply hr
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]
  · intro z hz
    set τ : ℍ := ⟨z, hz⟩ with hτ
    have hup : up jT z = GlobalTheory.modularJ τ := by
      simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rfl
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := by
      simp [Function.Periodic.qParam, hτ]
    have H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
      have := hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by
          simp [HahnSeries.coeff_single_of_ne hr])
      convert this using 1
      rw [hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z))
        (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) := by
      refine (Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective
        (fun r hr => ?_)).mp ?_
      · rw [h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]
      · convert hc τ using 1
        funext n
        simp only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
    convert H1.add H2 using 1
    · funext r
      rw [HahnSeries.coeff_add, map_add, add_mul]
    · rw [hup]
      ring
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]
  · intro r hr
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)),
      add_zero]
  · intro r
    by_cases h1 : r = -1
    · subst h1
      refine ⟨1, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]
      simp
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨c n, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]
    · push_neg at h2
      exact ⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩

end GlobalTheory.FNExpJ
