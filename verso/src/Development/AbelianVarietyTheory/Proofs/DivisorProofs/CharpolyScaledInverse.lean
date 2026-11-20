import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA`. Use `set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB`. Establish `hAB : A * B = 1` using `by simp [hA, hB]`. Establish `hcard : Multiset.card s = n`. Establish `h1` using `Matrix.charpoly_natDegree_eq_dim A`.

Rewrite `h1` using `[h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]`. Simplify using `using h1`. Establish `hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod`. Introduce `y`. Rewrite using `[← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]`.

Simplify using the standard rewrite rules. Establish `hdet : A.det * B.det = 1` using `by rw [← Matrix.det_mul, hAB, Matrix.det_one]`. Establish `hneg : (-A).det = (s.map fun a => -a).prod` using `by simpa using hev 0`. Establish `hne : (-A).det ≠ 0`. Rewrite using `[Matrix.det_neg]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)`. Establish `hs : ∀ a ∈ s, a ≠ 0`. Introduce `a ha h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hneg]`.

Conclude with `Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl` and prove the remaining obligations. Introduce `x hx`. Establish `hx0 : x ≠ 0` using `hx`.

Simplify using `only [Set.mem_setOf_eq]`. Rewrite using `[Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Establish `key : (-A) * (Matrix.scalar (Fin n) x - t • B) = x • (Matrix.scalar (Fin n) (t / x) - A)`. Rewrite using `[Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one, smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]`.

Normalize the expressions using the abelian group laws. Rewrite using `[← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin, ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a ha`.

Use `hs a ha` as an intermediate fact. Simplify using `only [Function.comp, eval_sub, eval_X, eval_C]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem charpoly_smul_inv_of_charpoly_eq_prod (n : ℕ) (M : GL (Fin n) ℂ) (t : ℂ) (s : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun a => X - C a).prod) :
    (t • ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)).charpoly
      = (s.map fun a => X - C (t * a⁻¹)).prod := by
  set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB
  have hAB : A * B = 1 := by simp [hA, hB]
  have hcard : Multiset.card s = n := by
    have h1 := Matrix.charpoly_natDegree_eq_dim A
    rw [h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1
  have hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod := by
    intro y
    rw [← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hneg : (-A).det = (s.map fun a => -a).prod := by simpa using hev 0
  have hne : (-A).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)
  have hs : ∀ a ∈ s, a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [hneg]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_setOf_eq]
  rw [Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have key : (-A) * (Matrix.scalar (Fin n) x - t • B)
      = x • (Matrix.scalar (Fin n) (t / x) - A) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one,
      smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]
    abel
  rw [← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin,
    ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have := hs a ha
  simp only [Function.comp, eval_sub, eval_X, eval_C]
  field_simp
  ring

end GlobalTheory
