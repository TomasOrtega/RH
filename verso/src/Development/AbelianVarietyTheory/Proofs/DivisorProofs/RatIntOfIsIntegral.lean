import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

open GlobalTheory.LKTorus

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
lemma LKTorus.rat_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Both sides reduce to the same expression. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Use the polynomial consequences of the given equalities and inequalities. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations.

Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem LKTorus.simT_integral_finite (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    {x : Lˣ | x ∈ simT ℚ c ∧ IsIntegral ℤ (x : L) ∧ IsIntegral ℤ ((x⁻¹ : Lˣ) : L)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le L ℂ 1
  refine (hF.preimage (Set.injOn_of_injective Units.val_injective)).subset ?_
  rintro x ⟨⟨t, ht⟩, hx, hxi⟩
  have hinv : x⁻¹ ∈ simT ℚ c := (simT ℚ c).inv_mem ⟨t, ht⟩
  obtain ⟨t', ht'⟩ := hinv
  have hcint : ∀ y : L, IsIntegral ℤ y → IsIntegral ℤ (c y) := fun y hy =>
    hy.map (c.toRingHom.toIntAlgHom)
  have hinj : Function.Injective (algebraMap ℚ L) := (algebraMap ℚ L).injective
  have htI : IsIntegral ℤ ((t : ℚ)) := by
    rw [← isIntegral_algebraMap_iff hinj, ← ht]
    exact hx.mul (hcint _ hx)
  have ht'I : IsIntegral ℤ ((t' : ℚ)) := by
    rw [← isIntegral_algebraMap_iff hinj, ← ht']
    exact hxi.mul (hcint _ hxi)
  obtain ⟨n, hn⟩ := LKTorus.rat_int_of_isIntegral htI
  obtain ⟨m, hm⟩ := LKTorus.rat_int_of_isIntegral ht'I
  have hprod : (t : ℚ) * t' = 1 := by
    apply hinj
    rw [map_mul, ← ht, ← ht', map_one]
    have h1 : ((x⁻¹ : Lˣ) : L) * (x : L) = 1 := by simp
    calc (x : L) * c x * (((x⁻¹ : Lˣ) : L) * c ((x⁻¹ : Lˣ) : L))
        = (((x⁻¹ : Lˣ) : L) * (x : L)) * c (((x⁻¹ : Lˣ) : L) * (x : L)) := by rw [map_mul]; ring
      _ = 1 := by rw [h1, map_one, one_mul]
  have hnm : n * m = 1 := by
    have : ((n * m : ℤ) : ℚ) = 1 := by push_cast; rw [hn, hm, hprod]
    exact_mod_cast this
  refine ⟨hx, fun τ => ?_⟩
  have hτ : ((‖τ x‖ ^ 2 : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    have e := congrArg τ ht
    rw [map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq, eq_ratCast, map_ratCast, ← hn] at e
    rw [e]; push_cast; rfl
  have hτ' : ‖τ x‖ ^ 2 = (n : ℝ) := by exact_mod_cast hτ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · rw [h] at hτ'
    have h0 : 0 ≤ ‖τ x‖ := norm_nonneg _
    push_cast at hτ'
    nlinarith
  · rw [h] at hτ'
    push_cast at hτ'
    nlinarith [sq_nonneg ‖τ x‖]

end GlobalTheory
