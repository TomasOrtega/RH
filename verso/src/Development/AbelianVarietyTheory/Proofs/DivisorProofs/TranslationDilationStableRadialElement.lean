import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def dilF (Φ : k → ℂ) (z : k) : k → ℂ := fun x => Φ (z * x)

/- English proof (translation)
Establish `hR0 : valuation k (R : k) ≠ 0` using `by simp`. Use function extensionality and compare the values at `x`. Simplify using `only [dilF]`. Distinguish the cases in `hx : valuation k x ≤ valuation k (R : k)`. Establish `e : w * x = z * x + (w - z) * x` using `by ring`.

Rewrite using `[e, hLC]`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `push_neg at hx`. Rewrite using `[hCS, hCS]`.

Simplify `hx` using `[map_mul, hz]`. Simplify `hx` using `[map_mul, hw]`.
-/
theorem dilF_eq_of_close {Φ : k → ℂ} (r R : kˣ)
    (hLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x)
    (hCS : ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0) {z w : k}
    (hz : valuation k z = 1) (hw : valuation k w = 1)
    (hzw : valuation k (w - z) ≤ valuation k (r : k) * (valuation k (R : k))⁻¹) :
    dilF Φ w = dilF Φ z := by
  have hR0 : valuation k (R : k) ≠ 0 := by simp
  funext x
  simp only [dilF]
  by_cases hx : valuation k x ≤ valuation k (R : k)
  · have e : w * x = z * x + (w - z) * x := by ring
    rw [e, hLC]
    rw [map_mul]
    calc valuation k (w - z) * valuation k x
        ≤ (valuation k (r : k) * (valuation k (R : k))⁻¹) * valuation k (R : k) := mul_le_mul' hzw hx
      _ = valuation k (r : k) := by rw [mul_assoc, inv_mul_cancel₀ hR0, mul_one]
  · push_neg at hx
    rw [hCS, hCS]
    · simpa [map_mul, hz] using hx
    · simpa [map_mul, hw] using hx

/- English proof (translation)
Use `set c : ValueGroupWithZero k := min (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with hc`. Establish `hc0 : c ≠ 0`. Rewrite using `[hc]`. Apply the tactic sequence `rcases min_choice (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with h | h <;> rw [h] <;> simp`. Set `U : k → Set k` to `fun z => {w : k | valuation k (w - z) < c}`.

Establish `hU : ∀ z ∈ {z : k | valuation k z ≤ 1}, U z ∈ nhds z` using `fun z _ => (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 c hc0, by`. Introduce `w hw`. Use `show valuation k (w - z) < c`. Simplify using `using hw⟩`. Take `⟨t, -, ht⟩` from `(IsNonarchimedeanLocalField.isCompact_closedBall k 1).elim_nhds_subcover U hU`.

Use `((t.finite_toSet).image (dilF Φ)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hw' : valuation k w = 1` using `hw`. Establish `hmem : w ∈ ⋃ z ∈ t, U z` using `ht (le_of_eq hw')`. Simplify using `only [Set.mem_iUnion, exists_prop] at hmem`.

Take `⟨z, hzt, hwz⟩` from `hmem`. Establish `hwz' : valuation k (w - z) < c` using `hwz`. Establish `hz1 : valuation k z = 1`. Establish `h1 : valuation k (z - w) < valuation k w`. Rewrite using `[hw', ← Valuation.map_neg, neg_sub]`.

Conclude with `lt_of_lt_of_le hwz' (min_le_right _ _)`. Conclude with `(Valuation.map_eq_of_sub_lt (valuation k) h1).trans hw'`. Use `⟨z, hzt, ?_⟩` and prove the remaining obligations. Conclude with `(dilF_eq_of_close r R hLC hCS hz1 hw' (le_trans hwz'.le (min_le_left _ _))).symm`.
-/
theorem finite_dilF {Φ : k → ℂ} (r R : kˣ)
    (hLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x)
    (hCS : ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0) :
    (dilF Φ '' {z : k | valuation k z = 1}).Finite := by
  set c : ValueGroupWithZero k := min (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    rcases min_choice (valuation k (r : k) * (valuation k (R : k))⁻¹) 1 with h | h <;> rw [h] <;> simp
  let U : k → Set k := fun z => {w : k | valuation k (w - z) < c}
  have hU : ∀ z ∈ {z : k | valuation k z ≤ 1}, U z ∈ nhds z := fun z _ =>
    (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 c hc0, by
      intro w hw
      show valuation k (w - z) < c
      simpa using hw⟩
  obtain ⟨t, -, ht⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall k 1).elim_nhds_subcover U hU
  refine ((t.finite_toSet).image (dilF Φ)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : valuation k w = 1 := hw
  have hmem : w ∈ ⋃ z ∈ t, U z := ht (le_of_eq hw')
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨z, hzt, hwz⟩ := hmem
  have hwz' : valuation k (w - z) < c := hwz
  have hz1 : valuation k z = 1 := by
    have h1 : valuation k (z - w) < valuation k w := by
      rw [hw', ← Valuation.map_neg, neg_sub]
      exact lt_of_lt_of_le hwz' (min_le_right _ _)
    exact (Valuation.map_eq_of_sub_lt (valuation k) h1).trans hw'
  refine ⟨z, hzt, ?_⟩
  exact (dilF_eq_of_close r R hLC hCS hz1 hw' (le_trans hwz'.le (min_le_left _ _))).symm

/- English proof (translation)
Introduce `k _ _ _ _ W htr hdil Φ hΦW hΦ0 hLC hCS`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, Φ x₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hΦ0 (funext h)`.

Take `⟨r, hr⟩` from `hLC`. Take `⟨R₀, hR₀⟩` from `hCS`. Use `set Ψ : k → ℂ := fun x => Φ (x + x₀) with hΨ`. Establish `hΨW : Ψ ∈ W` using `htr Φ hΦW x₀`. Establish `hΨ0 : Ψ 0 ≠ 0` using `by simpa [Ψ] using hx₀`.

Establish `hΨLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Ψ (x + y) = Ψ x`. Introduce `x y hy`. Simplify using `only [Ψ]`. Rewrite using `[add_right_comm]`. Conclude with `hr _ _ hy`.

Establish `hx₀R : valuation k x₀ ≤ valuation k (R₀ : k)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx₀ (hR₀ _ h)`. Establish `hΨCS : ∀ x : k, valuation k (R₀ : k) < valuation k x → Ψ x = 0`.

Introduce `x hx`. Apply `hR₀` to reduce the goal to its premises. Rewrite using `[Valuation.map_add_eq_of_lt_left (valuation k) (lt_of_le_of_lt hx₀R hx)]`. Conclude with `hx`. Establish `hS` using `finite_dilF r R₀ hΨLC hΨCS`.

Use `set T := hS.toFinset with hT`. Establish `hmemT : ∀ ψ ∈ T, ∃ z : k, valuation k z = 1 ∧ dilF Ψ z = ψ`. Introduce `ψ hψ`. Rewrite `hψ` using `[hT, Set.Finite.mem_toFinset]`. Conclude with `hψ`.

Establish `happ : ∀ x : k, (∑ ψ ∈ T, ψ) x = ∑ ψ ∈ T, ψ x` using `fun x => Finset.sum_apply x T fun ψ => ψ`. Use `⟨∑ ψ ∈ T, ψ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem W fun ψ hψ => ?_` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Establish `hz0 : z ≠ 0`.

Introduce `h`. Rewrite `hz` using `[h, map_zero]`. Conclude with `zero_ne_one hz`. Use `show (fun x => Ψ (z * x)) ∈ W`. Simplify using `using hdil Ψ hΨW (Units.mk0 z hz0)`.

Use `⟨r, fun x y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[happ, happ]`. Use `Finset.sum_congr rfl fun ψ hψ => ?_` and prove the remaining obligations. Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Simplify using `only [dilF]`.

Rewrite using `[mul_add, hΨLC]`. Simplify `hy` using `[map_mul, hz]`. Use `⟨R₀, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[happ]`. Use `Finset.sum_eq_zero fun ψ hψ => ?_` and prove the remaining obligations.

Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Simplify using `only [dilF]`. Apply `hΨCS` to reduce the goal to its premises. Simplify `hx` using `[map_mul, hz]`. Rewrite using `[happ]`.

Establish `h1 : ∀ ψ ∈ T, ψ 0 = Ψ 0`. Introduce `ψ hψ`. Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Simplify using `[dilF]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]`.

Use `mul_ne_zero ?_ hΨ0` and prove the remaining obligations. Establish `hne : T.Nonempty` using `⟨dilF Ψ 1, by rw [hT, Set.Finite.mem_toFinset]; exact ⟨1, by simp, rfl⟩⟩`. Conclude with `hne.card_pos.ne'` after adjusting the coercions. Introduce `u x hu`. Rewrite using `[happ, happ]`.

Use `Finset.sum_nbij' (fun ψ => fun y => ψ ((u : k) * y)) (fun ψ => fun y => ψ (((u⁻¹ : kˣ) : k) * y)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `ψ hψ`. Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Rewrite using `[hT, Set.Finite.mem_toFinset]`. Use `⟨z * u, by simp [map_mul, hz, hu], ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `y`. Simplify using `[dilF, mul_assoc]`. Introduce `ψ hψ`. Take `⟨z, hz, rfl⟩` from `hmemT ψ hψ`. Rewrite using `[hT, Set.Finite.mem_toFinset]`.

Establish `hu' : valuation k (((u⁻¹ : kˣ) : k)) = 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]`. Use `⟨z * ((u⁻¹ : kˣ) : k), by show valuation k (z * ((u⁻¹ : kˣ) : k)) = 1` and prove the remaining obligations. Rewrite using `[map_mul, hz, hu', mul_one], ?_⟩`. Use function extensionality and compare the values at `y`.

Simplify using `[dilF, mul_assoc]`. Introduce `ψ _`. Use function extensionality and compare the values at `y`. Simplify using `[← mul_assoc]`. Introduce `ψ _`.

Use function extensionality and compare the values at `y`. Simplify using `[← mul_assoc]`. Introduce `ψ _`. Both sides reduce to the same expression.
-/
theorem exists_radial_mem_of_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) →
    (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ Φ ∈ W, Φ ≠ 0 → GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ →
    ∃ R ∈ W, GlobalTheory.PrinTwo.IsLC R ∧ GlobalTheory.PrinTwo.IsCS R ∧ R 0 ≠ 0 ∧
      ∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x := by
  intro k _ _ _ _ W htr hdil Φ hΦW hΦ0 hLC hCS
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (funext h)
  obtain ⟨r, hr⟩ := hLC
  obtain ⟨R₀, hR₀⟩ := hCS
  set Ψ : k → ℂ := fun x => Φ (x + x₀) with hΨ
  have hΨW : Ψ ∈ W := htr Φ hΦW x₀
  have hΨ0 : Ψ 0 ≠ 0 := by simpa [Ψ] using hx₀
  have hΨLC : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Ψ (x + y) = Ψ x := by
    intro x y hy
    simp only [Ψ]
    rw [add_right_comm]
    exact hr _ _ hy
  have hx₀R : valuation k x₀ ≤ valuation k (R₀ : k) := by
    by_contra h
    push_neg at h
    exact hx₀ (hR₀ _ h)
  have hΨCS : ∀ x : k, valuation k (R₀ : k) < valuation k x → Ψ x = 0 := by
    intro x hx
    apply hR₀
    rw [Valuation.map_add_eq_of_lt_left (valuation k) (lt_of_le_of_lt hx₀R hx)]
    exact hx
  have hS := finite_dilF r R₀ hΨLC hΨCS
  set T := hS.toFinset with hT
  have hmemT : ∀ ψ ∈ T, ∃ z : k, valuation k z = 1 ∧ dilF Ψ z = ψ := by
    intro ψ hψ
    rw [hT, Set.Finite.mem_toFinset] at hψ
    exact hψ
  have happ : ∀ x : k, (∑ ψ ∈ T, ψ) x = ∑ ψ ∈ T, ψ x := fun x => Finset.sum_apply x T fun ψ => ψ
  refine ⟨∑ ψ ∈ T, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem W fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, map_zero] at hz
      exact zero_ne_one hz
    show (fun x => Ψ (z * x)) ∈ W
    simpa using hdil Ψ hΨW (Units.mk0 z hz0)
  · refine ⟨r, fun x y hy => ?_⟩
    rw [happ, happ]
    refine Finset.sum_congr rfl fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    simp only [dilF]
    rw [mul_add, hΨLC]
    simpa [map_mul, hz] using hy
  · refine ⟨R₀, fun x hx => ?_⟩
    rw [happ]
    refine Finset.sum_eq_zero fun ψ hψ => ?_
    obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
    simp only [dilF]
    apply hΨCS
    simpa [map_mul, hz] using hx
  · rw [happ]
    have h1 : ∀ ψ ∈ T, ψ 0 = Ψ 0 := by
      intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      simp [dilF]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    refine mul_ne_zero ?_ hΨ0
    have hne : T.Nonempty := ⟨dilF Ψ 1, by rw [hT, Set.Finite.mem_toFinset]; exact ⟨1, by simp, rfl⟩⟩
    exact_mod_cast hne.card_pos.ne'
  · intro u x hu
    rw [happ, happ]
    refine Finset.sum_nbij' (fun ψ => fun y => ψ ((u : k) * y)) (fun ψ => fun y => ψ (((u⁻¹ : kˣ) : k) * y))
      ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      rw [hT, Set.Finite.mem_toFinset]
      refine ⟨z * u, by simp [map_mul, hz, hu], ?_⟩
      funext y
      simp [dilF, mul_assoc]
    · intro ψ hψ
      obtain ⟨z, hz, rfl⟩ := hmemT ψ hψ
      rw [hT, Set.Finite.mem_toFinset]
      have hu' : valuation k (((u⁻¹ : kˣ) : k)) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
      refine ⟨z * ((u⁻¹ : kˣ) : k), by
        show valuation k (z * ((u⁻¹ : kˣ) : k)) = 1
        rw [map_mul, hz, hu', mul_one], ?_⟩
      funext y
      simp [dilF, mul_assoc]
    · intro ψ _
      funext y
      simp [← mul_assoc]
    · intro ψ _
      funext y
      simp [← mul_assoc]
    · intro ψ _
      rfl

end GlobalTheory.PrinTwo
