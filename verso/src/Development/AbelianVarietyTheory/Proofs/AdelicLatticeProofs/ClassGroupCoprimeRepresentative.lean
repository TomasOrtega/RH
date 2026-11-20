import Mathlib
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ m hm c`. Take `⟨J, hJ⟩` from `ClassGroup.mk0_surjective c⁻¹`. Establish `hJ0 : (J : Ideal (𝓞 K)) ≠ 0` using `nonZeroDivisors.coe_ne_zero J`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : (J : Ideal (𝓞 K)) * m ≤ J) (mul_ne_zero hJ0 hm)`. Establish `haJ : a ∈ (J : Ideal (𝓞 K))` using `ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`.

Take `⟨L, hL⟩ : (J : Ideal (𝓞 K)) ∣ Ideal.span {a}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)`. Establish `hcop : m ⊔ L = ⊤`. Establish `h1 : (J : Ideal (𝓞 K)) * (m ⊔ L) = J * ⊤`. Rewrite using `[Ideal.mul_sup, ← hL, ha, Ideal.mul_top]`. Conclude with `mul_left_cancel₀ hJ0 h1`.

Distinguish the cases in `hL0 : L = 0`. Establish `hmt : m = ⊤` using `by simpa [hL0] using hcop`. Take `⟨b, hb⟩` from `ClassGroup.mk0_surjective c`. Conclude with `⟨b, hb, by simp [hmt]⟩`. Use `⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, ?_, by rw [sup_comm]; exact hcop⟩` and prove the remaining obligations.

Establish `hprod : ClassGroup.mk0 J * ClassGroup.mk0 ⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩ = 1`. Rewrite using `[← map_mul, ClassGroup.mk0_eq_one_iff]`. Express the relevant statement in the definitionally equal form `((J : Ideal (𝓞 K)) * L).IsPrincipal`. Rewrite using `[← hL]`. Conclude with `⟨⟨a, rfl⟩⟩`.

Rewrite `hprod` using `[hJ]`. Conclude with `(inv_mul_eq_one.mp hprod).symm`.
-/
theorem exists_integral_ideal_in_class_coprime :
    ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)), m ≠ ⊥ → ∀ c : ClassGroup (𝓞 K), ∃ b : (Ideal (𝓞 K))⁰, ClassGroup.mk0 b = c ∧ (b : Ideal (𝓞 K)) ⊔ m = ⊤ := by
  intro K _ _ m hm c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (Ideal.mul_le_inf.trans inf_le_left : (J : Ideal (𝓞 K)) * m ≤ J) (mul_ne_zero hJ0 hm)
  have haJ : a ∈ (J : Ideal (𝓞 K)) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨L, hL⟩ : (J : Ideal (𝓞 K)) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)
  have hcop : m ⊔ L = ⊤ := by
    have h1 : (J : Ideal (𝓞 K)) * (m ⊔ L) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hL, ha, Ideal.mul_top]
    exact mul_left_cancel₀ hJ0 h1
  by_cases hL0 : L = 0
  · have hmt : m = ⊤ := by simpa [hL0] using hcop
    obtain ⟨b, hb⟩ := ClassGroup.mk0_surjective c
    exact ⟨b, hb, by simp [hmt]⟩
  · refine ⟨⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩, ?_, by rw [sup_comm]; exact hcop⟩
    have hprod : ClassGroup.mk0 J * ClassGroup.mk0 ⟨L, mem_nonZeroDivisors_of_ne_zero hL0⟩ = 1 := by
      rw [← map_mul, ClassGroup.mk0_eq_one_iff]
      change ((J : Ideal (𝓞 K)) * L).IsPrincipal
      rw [← hL]
      exact ⟨⟨a, rfl⟩⟩
    rw [hJ] at hprod
    exact (inv_mul_eq_one.mp hprod).symm

end GlobalTheory
