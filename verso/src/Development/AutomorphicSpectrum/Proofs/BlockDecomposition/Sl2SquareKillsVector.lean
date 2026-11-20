import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

/- English proof (translation)
Introduce `n Z _ _ E hG hA i j hij a ha p r hp hr hm hd hor`. Establish `hji : j ≠ i` using `hij.symm`. Establish `c1 : ∀ v, E i j (E j i v) - E j i (E i j v) = E i i v - E j j v`. Introduce `v`. Establish `h` using `LinearMap.congr_fun (hG i j j i) v`.

Simplify `h` using `[Module.End.mul_apply]`. Establish `c2 : ∀ v, E i i (E i j v) - E i j (E i i v) = E i j v`. Introduce `v`. Establish `h` using `LinearMap.congr_fun (hG i i i j) v`. Simplify `h` using `[Module.End.mul_apply, hji]`.

Establish `c3 : ∀ v, E j j (E i j v) - E i j (E j j v) = - E i j v`. Introduce `v`. Establish `h` using `LinearMap.congr_fun (hG j j i j) v`. Simplify `h` using `[Module.End.mul_apply, hji]`. Establish `hsq : ((E i j) ^ 2) a = E i j (E i j a)`.

Simplify using `[pow_two, Module.End.mul_apply]`. Rewrite using `[hsq]`. Break down `hor with h | h` into its components or cases. Simplify using `[h]`. Establish `hYX : E j i (E i j a) = ((r : ℂ) - p) • a`.

Establish `h1` using `c1 a`. Rewrite `h1` using `[h, map_zero, hp, hr, zero_sub]`. Rewrite using `[sub_smul, ← neg_sub ((p : ℂ) • a), ← h1, neg_neg]`. Establish `hn : ‖E i j a‖ ^ 2 = (r - p) * ‖a‖ ^ 2`. Establish `h1 : ⟪E i j a, E i j a⟫_ℂ = ((r : ℂ) - p) * ⟪a, a⟫_ℂ`.

Rewrite using `[hA, hYX, inner_smul_right]`. Rewrite `h1` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h2 : (((‖E i j a‖ ^ 2 : ℝ)) : ℂ) = (((r - p) * ‖a‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Simplify using `using h1`.

Conclude with `h2` after adjusting the coercions. Establish `hapos : 0 < ‖a‖ ^ 2` using `by positivity`. Establish `hle : 0 ≤ r - p`. Assume the negation of the conclusion as `hc`. Establish `: (r - p) * ‖a‖ ^ 2 < 0` using `mul_neg_of_neg_of_pos (not_le.mp hc) hapos`.

Use polynomial arithmetic with `[sq_nonneg ‖E i j a‖]`. Take `⟨m, hm⟩` from `hm`. Establish `hm1 : (-1 : ℤ) ≤ m`. Establish `: ((-1 : ℤ) : ℝ) ≤ (m : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions.

Establish `hm2 : m ≤ 0`. Establish `: (m : ℝ) ≤ ((0 : ℤ) : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `hcases : m = 0 ∨ m = -1` using `by omega`. Break down `hcases with h0 | h0` into its components or cases.

Establish `hpr : r - p = 0` using `by rw [h0] at hm; push_cast at hm; linarith`. Rewrite `hn` using `[hpr, zero_mul]`. Establish `h3 : E i j a = 0`. Establish `: ‖E i j a‖ = 0` using `by simpa using hn`. Conclude with `norm_eq_zero.mp this`.

Simplify using `[h3]`. Establish `hpr : r - p = 1` using `by rw [h0] at hm; push_cast at hm; linarith`. Establish `hprC : (r : ℂ) - p = 1` using `by exact_mod_cast hpr`. Establish `hYX' : E j i (E i j a) = a` using `by rw [hYX, hprC, one_smul]`. Establish `e1 : E i i (E i j a) = ((p : ℂ) + 1) • E i j a`.

Establish `h1` using `c2 a`. Rewrite `h1` using `[hp, map_smul]`. Rewrite using `[add_smul, one_smul, add_comm]`. Conclude with `sub_eq_iff_eq_add.mp h1`. Establish `e2 : E j j (E i j a) = ((r : ℂ) - 1) • E i j a`.

Establish `h1` using `c3 a`. Rewrite `h1` using `[hr, map_smul]`. Rewrite using `[sub_smul, one_smul, sub_eq_add_neg, ← h1]`. Normalize the expressions using the abelian group laws. Establish `hY2 : E j i (E i j (E i j a)) = 0`.

Establish `h1` using `c1 (E i j a)`. Rewrite `h1` using `[hYX', e1, e2]`. Establish `h2 : E j i (E i j (E i j a)) = (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) • E i j a`. Rewrite using `[sub_smul, sub_smul, one_smul, ← h1]`. Normalize the expressions using the abelian group laws.

Establish `h3 : (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) = 0`. Take the linear combination `hprC`. Rewrite using `[h2, h3, zero_smul]`. Establish `h4 : ⟪E i j (E i j a), E i j (E i j a)⟫_ℂ = 0`. Rewrite using `[hA, hY2, inner_zero_right]`.

Conclude with `inner_self_eq_zero.mp h4`.
-/
theorem sl2_square_kills : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  intro n Z _ _ E hG hA i j hij a ha p r hp hr hm hd hor
  have hji : j ≠ i := hij.symm
  have c1 : ∀ v, E i j (E j i v) - E j i (E i j v) = E i i v - E j j v := by
    intro v
    have h := LinearMap.congr_fun (hG i j j i) v
    simpa [Module.End.mul_apply] using h
  have c2 : ∀ v, E i i (E i j v) - E i j (E i i v) = E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG i i i j) v
    simpa [Module.End.mul_apply, hji] using h
  have c3 : ∀ v, E j j (E i j v) - E i j (E j j v) = - E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG j j i j) v
    simpa [Module.End.mul_apply, hji] using h
  have hsq : ((E i j) ^ 2) a = E i j (E i j a) := by
    simp [pow_two, Module.End.mul_apply]
  rw [hsq]
  rcases hor with h | h
  · simp [h]
  have hYX : E j i (E i j a) = ((r : ℂ) - p) • a := by
    have h1 := c1 a
    rw [h, map_zero, hp, hr, zero_sub] at h1
    rw [sub_smul, ← neg_sub ((p : ℂ) • a), ← h1, neg_neg]
  have hn : ‖E i j a‖ ^ 2 = (r - p) * ‖a‖ ^ 2 := by
    have h1 : ⟪E i j a, E i j a⟫_ℂ = ((r : ℂ) - p) * ⟪a, a⟫_ℂ := by
      rw [hA, hYX, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : (((‖E i j a‖ ^ 2 : ℝ)) : ℂ) = (((r - p) * ‖a‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h1
    exact_mod_cast h2
  have hapos : 0 < ‖a‖ ^ 2 := by positivity
  have hle : 0 ≤ r - p := by
    by_contra hc
    have : (r - p) * ‖a‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) hapos
    nlinarith [sq_nonneg ‖E i j a‖]
  obtain ⟨m, hm⟩ := hm
  have hm1 : (-1 : ℤ) ≤ m := by
    have : ((-1 : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hm2 : m ≤ 0 := by
    have : (m : ℝ) ≤ ((0 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcases : m = 0 ∨ m = -1 := by omega
  rcases hcases with h0 | h0
  · have hpr : r - p = 0 := by rw [h0] at hm; push_cast at hm; linarith
    rw [hpr, zero_mul] at hn
    have h3 : E i j a = 0 := by
      have : ‖E i j a‖ = 0 := by simpa using hn
      exact norm_eq_zero.mp this
    simp [h3]
  · have hpr : r - p = 1 := by rw [h0] at hm; push_cast at hm; linarith
    have hprC : (r : ℂ) - p = 1 := by exact_mod_cast hpr
    have hYX' : E j i (E i j a) = a := by rw [hYX, hprC, one_smul]
    have e1 : E i i (E i j a) = ((p : ℂ) + 1) • E i j a := by
      have h1 := c2 a
      rw [hp, map_smul] at h1
      rw [add_smul, one_smul, add_comm]
      exact sub_eq_iff_eq_add.mp h1
    have e2 : E j j (E i j a) = ((r : ℂ) - 1) • E i j a := by
      have h1 := c3 a
      rw [hr, map_smul] at h1
      rw [sub_smul, one_smul, sub_eq_add_neg, ← h1]
      abel
    have hY2 : E j i (E i j (E i j a)) = 0 := by
      have h1 := c1 (E i j a)
      rw [hYX', e1, e2] at h1
      have h2 : E j i (E i j (E i j a)) =
          (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) • E i j a := by
        rw [sub_smul, sub_smul, one_smul, ← h1]
        abel
      have h3 : (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) = 0 := by
        linear_combination hprC
      rw [h2, h3, zero_smul]
    have h4 : ⟪E i j (E i j a), E i j (E i j a)⟫_ℂ = 0 := by
      rw [hA, hY2, inner_zero_right]
    exact inner_self_eq_zero.mp h4

end GlobalTheory.CompanionTheory.RealCount
