import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

/- English proof (translation)
Establish `hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ))`. Introduce `a a' h`. Establish `h1` using `hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by`. Simplify using `only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`. Conclude with `mul_inv_eq_one.2 h)`.

Use function extensionality and compare the values at `i`. Establish `h2` using `h1 i`. Rewrite `h2` using `[zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one]`. Conclude with `Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)`. Simplify using `using Fintype.card_le_of_injective _ hinj`.
-/
theorem prod_orderOf_le_card_of_indep {G ι : Type} [CommGroup G] [Fintype G] [Fintype ι] (x : ι → G)
    (hx : ∀ a : ι → ℤ, ∏ i, x i ^ a i = 1 → ∀ i, x i ^ a i = 1) : ∏ i, orderOf (x i) ≤ Fintype.card G := by
  classical
  have hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ)) := by
    intro a a' h
    have h1 := hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 h)
    funext i
    have h2 := h1 i
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h2
    exact Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)
  simpa using Fintype.card_le_of_injective _ hinj

/- English proof (translation)
Use `Nat.le_log_of_pow_le (by norm_num) ?_` and prove the remaining obligations. Establish `h1 : ∏ i, b.h i ≤ classNumber E` using `prod_orderOf_le_card_of_indep _ b.indep`. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter_ne_one]`. Use `Finset.pow_card_le_prod _ _ _ fun i hi => ?_` and prove the remaining obligations.

Establish `h2` using `(Finset.mem_filter.1 hi).2`. Establish `h3` using `b.h_pos i`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_filter_le_log_classNumber {E : Type} [Field E] [NumberField E] (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis E) :
    (Finset.univ.filter fun i => b.h i ≠ 1).card ≤ Nat.log 2 (classNumber E) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
  refine le_trans ?_ h1
  rw [← Finset.prod_filter_ne_one]
  refine Finset.pow_card_le_prod _ _ _ fun i hi => ?_
  have h2 := (Finset.mem_filter.1 hi).2
  have h3 := b.h_pos i
  omega

/- English proof (translation)
Use `choose ψ hψ using fun i : Fin b.k => IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)`. Use `⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ, Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩`. Rewrite using `[kPsiField_eq H b p q ψ hψ]`.

Use `le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `h : b.h i = 1`. Establish `h1 : ψ i ∈ imField H.φ₀` using `⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩`.

Conclude with `(le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1`. Conclude with `(le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))`. Introduce `y hy`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hy)`. Conclude with `⟨i, rfl⟩`.
-/
theorem exists_kPsiField_generators (R : Ranks) (H : Host R) (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis H.E) (p q : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ Nat.log 2 (classNumber H.E) ∧
      (∀ y ∈ S, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber H.E ∧ y ^ n ∈ imField H.φ₀) ∧
      kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (S : Set ℂ) := by
  classical
  choose ψ hψ using fun i : Fin b.k =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)
  refine ⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ,
    Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩
  · rw [kPsiField_eq H b p q ψ hψ]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases h : b.h i = 1
      · have h1 : ψ i ∈ imField H.φ₀ := ⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩
        exact (le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1
      · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _
          (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨i, rfl⟩

end GlobalTheory.Mem.Fld
