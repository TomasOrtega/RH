import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

open GlobalTheory.LKTorus

namespace GlobalTheory

/- English proof (translation)
Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Conclude with `⟨n, by simpa using hn⟩`.
-/
lemma LKTorus.rat_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

/- English proof (translation)
Establish `hF` using `NumberField.Embeddings.finite_of_norm_le L ℂ 1`. Use `(hF.preimage (Set.injOn_of_injective Units.val_injective)).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨⟨t, ht⟩, hx, hxi⟩`. Establish `hinv : x⁻¹ ∈ simT ℚ c` using `(simT ℚ c).inv_mem ⟨t, ht⟩`. Take `⟨t', ht'⟩` from `hinv`.

Establish `hcint : ∀ y : L, IsIntegral ℤ y → IsIntegral ℤ (c y)` using `fun y hy => hy.map (c.toRingHom.toIntAlgHom)`. Establish `hinj : Function.Injective (algebraMap ℚ L)` using `(algebraMap ℚ L).injective`. Establish `htI : IsIntegral ℤ ((t : ℚ))`. Rewrite using `[← isIntegral_algebraMap_iff hinj, ← ht]`. Conclude with `hx.mul (hcint _ hx)`.

Establish `ht'I : IsIntegral ℤ ((t' : ℚ))`. Rewrite using `[← isIntegral_algebraMap_iff hinj, ← ht']`. Conclude with `hxi.mul (hcint _ hxi)`. Take `⟨n, hn⟩` from `LKTorus.rat_int_of_isIntegral htI`. Take `⟨m, hm⟩` from `LKTorus.rat_int_of_isIntegral ht'I`.

Establish `hprod : (t : ℚ) * t' = 1`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, ← ht, ← ht', map_one]`. Establish `h1 : ((x⁻¹ : Lˣ) : L) * (x : L) = 1` using `by simp`. Combine the equalities or inequalities in the displayed calculation.

Establish `hnm : n * m = 1`. Establish `: ((n * m : ℤ) : ℚ) = 1` using `by push_cast; rw [hn, hm, hprod]`. Conclude with `this` after adjusting the coercions. Use `⟨hx, fun τ => ?_⟩` and prove the remaining obligations. Establish `hτ : ((‖τ x‖ ^ 2 : ℝ) : ℂ) = ((n : ℝ) : ℂ)`.

Establish `e` using `congrArg τ ht`. Rewrite `e` using `[map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq, eq_ratCast, map_ratCast, ← hn]`. Rewrite using `[e]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hτ' : ‖τ x‖ ^ 2 = (n : ℝ)` using `by exact_mod_cast hτ`. Break down `Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h` into its components or cases. Rewrite `hτ'` using `[h]`. Establish `h0 : 0 ≤ ‖τ x‖` using `norm_nonneg _`. Move the coercions through the operations in `at hτ'`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite `hτ'` using `[h]`. Move the coercions through the operations in `at hτ'`. Use polynomial arithmetic with `[sq_nonneg ‖τ x‖]`.
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
