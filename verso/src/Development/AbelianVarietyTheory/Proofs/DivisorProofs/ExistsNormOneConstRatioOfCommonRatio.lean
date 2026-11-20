import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEq

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ I S hS hc A B t hA hB ht hn`. Distinguish the cases in `h0 : ∀ i, ∀ x ∈ S, B i x = 0`. Use `⟨1, norm_one, fun i x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[ht i x hx, h0 i x hx, mul_zero, mul_zero]`. Simplify using `only [not_forall] at h0`.

Take `⟨i₀, x₀, hx₀, hne⟩` from `h0`. Take `⟨_, c, hcc⟩` from `exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀) (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)`. Use `⟨c, ?_, fun i x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hn i₀ x₀ hx₀`. Rewrite `h1` using `[hcc x₀ hx₀, norm_mul]`.

Conclude with `mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)`. Establish `hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S` using `(hA i).sub ((hB i).const_mul c)`. Use `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by` as an intermediate fact. Establish `e1` using `ht i y hy`. Establish `e2` using `ht i₀ y hy`.

Establish `e3 : A i₀ y = c * B i₀ y` using `hcc y hy`. Use `show B i₀ y * (A i y - c * B i y) = 0`. Rewrite using `[e1]`. Take the linear combination `(B i y) * (e3 - e2)) hx₀ hne x hx`. Conclude with `sub_eq_zero.mp this`.
-/
theorem exists_norm_one_const_ratio_of_common_ratio :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (I : Type) (S : Set V),
      IsOpen S → IsPreconnected S → ∀ (A B : I → V → ℂ) (t : V → ℂ), (∀ i, DifferentiableOn ℂ (A i) S) →
      (∀ i, DifferentiableOn ℂ (B i) S) → (∀ i, ∀ x ∈ S, A i x = t x * B i x) →
      (∀ i, ∀ x ∈ S, ‖A i x‖ = ‖B i x‖) → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ i, ∀ x ∈ S, A i x = ε * B i x := by
  intro V _ _ _ I S hS hc A B t hA hB ht hn
  by_cases h0 : ∀ i, ∀ x ∈ S, B i x = 0
  · refine ⟨1, norm_one, fun i x hx => ?_⟩
    rw [ht i x hx, h0 i x hx, mul_zero, mul_zero]
  · simp only [not_forall] at h0
    obtain ⟨i₀, x₀, hx₀, hne⟩ := h0
    obtain ⟨_, c, hcc⟩ := exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀)
      (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)
    refine ⟨c, ?_, fun i x hx => ?_⟩
    · have h1 := hn i₀ x₀ hx₀
      rw [hcc x₀ hx₀, norm_mul] at h1
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)
    · have hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S := (hA i).sub ((hB i).const_mul c)
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by
        have e1 := ht i y hy
        have e2 := ht i₀ y hy
        have e3 : A i₀ y = c * B i₀ y := hcc y hy
        show B i₀ y * (A i y - c * B i y) = 0
        rw [e1]
        linear_combination (B i y) * (e3 - e2)) hx₀ hne x hx
      exact sub_eq_zero.mp this

end GlobalTheory
