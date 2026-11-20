import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.GoodTop

namespace MixSubst

variable {n : ℕ}

/- English proof (translation)
Establish `h : (Matrix.of fun i d => ∑ c, x i c * k i c d) = fun i => ∑ c, x i c • k i c`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `(Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _ = _`.

Rewrite using `[← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem det_rows_sum (x : Fin n → Fin n → ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    (Matrix.of fun i d => ∑ c, x i c * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, x i (c i)) * (Matrix.of fun i d => k i (c i) d).det := by
  have h : (Matrix.of fun i d => ∑ c, x i c * k i c d) = fun i => ∑ c, x i c • k i c := by
    ext i j
    simp
  rw [h]
  change (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _ = _
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply']`. Both sides reduce to the same expression.
-/
theorem sum_sign_prod (J : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * ∏ i, J (c i) (u i) = (J.submatrix c id).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/- English proof (translation)
Establish `h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det = ∑ c : Fin n → Fin n, (∏ i, J (c i) (u i)) * (Matrix.of fun i d => k i (c i) d).det` using `fun u => det_rows_sum (fun i c => J c (u i)) k`. Repeatedly rewrite using `[h1, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← mul_assoc, ← Finset.sum_mul, sum_sign_prod]`. Use `symm`.

Use `Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) DFunLike.coe_injective _ _ (fun c hc => ?_) (fun σ => ?_)` and prove the remaining obligations. Establish `hinj : ¬ Function.Injective c` using `fun h => hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp h), rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by`. Simplify using `only [Function.Injective, not_forall] at hinj`. Take `⟨i, j, h, h'⟩` from `hinj`.

Conclude with `⟨i, j, h, h'⟩`. Rewrite using `[Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]), zero_mul]`. Rewrite using `[Matrix.det_permute, mul_comm J.det]`.
-/
theorem alt_sum (J : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      J.det * ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i d => ∑ c, J c (u i) * k i c d).det =
      ∑ c : Fin n → Fin n, (∏ i, J (c i) (u i)) * (Matrix.of fun i d => k i (c i) d).det :=
    fun u => det_rows_sum (fun i c => J c (u i)) k
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, sum_sign_prod]
  symm
  refine Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n)) DFunLike.coe_injective _ _
    (fun c hc => ?_) (fun σ => ?_)
  · have hinj : ¬ Function.Injective c := fun h =>
      hc ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp h), rfl⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h, h'⟩ := hinj
      exact ⟨i, j, h, h'⟩
    rw [Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]), zero_mul]
  · rw [Matrix.det_permute, mul_comm J.det]

/- English proof (translation)
Establish `h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d) = (Matrix.of fun i d => ∑ c, J c (u i) * k i c d) * J'`. Introduce `u`. Use extensionality with `i b`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Repeatedly rewrite using `[h1, Matrix.det_mul, ← mul_assoc, ← Finset.sum_mul]`. Rewrite using `[alt_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alt_sum_two (J J' : Matrix (Fin n) (Fin n) ℂ) (k : Fin n → Fin n → Fin n → ℂ) :
    ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d).det =
      J.det * J'.det *
        ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign u : ℤ) : ℂ) * (Matrix.of fun i d => k i (u i) d).det := by
  have h1 : ∀ u : Equiv.Perm (Fin n), (Matrix.of fun i b => ∑ c, ∑ d, J c (u i) * J' d b * k i c d) =
      (Matrix.of fun i d => ∑ c, J c (u i) * k i c d) * J' := by
    intro u
    ext i b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [h1, Matrix.det_mul, ← mul_assoc, ← Finset.sum_mul]
  rw [alt_sum]
  ring

end MixSubst

/- English proof (translation)
Unfold `mixTop`. Rewrite using `[mul_left_comm]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[mul_assoc ((Equiv.Perm.sign π : ℤ) : ℂ), ← Finset.mul_sum]`. Rewrite using `[mul_left_comm, ← MixSubst.alt_sum_two J J' (fun i c d => K i c d (p i) (p (π i)))]`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem mixTop_subst {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r)
    (J J' : Matrix (Fin n) (Fin n) ℂ) :
    mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  unfold mixTop
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp_rw [mul_assoc ((Equiv.Perm.sign π : ℤ) : ℂ), ← Finset.mul_sum]
  rw [mul_left_comm, ← MixSubst.alt_sum_two J J' (fun i c d => K i c d (p i) (p (π i)))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GlobalTheory.GoodTop
