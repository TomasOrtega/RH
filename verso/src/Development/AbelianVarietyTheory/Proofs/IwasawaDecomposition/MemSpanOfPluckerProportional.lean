import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

noncomputable section

namespace GlobalTheory.FlagEmb

/- English proof (translation)
Establish `h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s = ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]`. Simplify using `only [plk, Equiv.apply_symm_apply, id]`. Use `congr 1`.

Use extensionality with `l l'`. Distinguish the cases in `h : l' = i`. Substitute `h` using the available equality. Simplify using `[Matrix.updateCol_apply]`. Simplify using `[Matrix.updateCol_apply, Function.update_of_ne h, h]`.
-/
theorem adjugate_mul_eq_plk {K : Type} [Field K] {M k : ℕ} (D : Fin k → Fin (M + 1) → K) (r : Fin k → Fin (M + 1))
    (i : Fin k) (s : Fin (M + 1)) :
    ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      plk D id ((plE M k).symm (Function.update r i s)) := by
  have h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [plk, Equiv.apply_symm_apply, id]
  congr 1
  ext l l'
  by_cases h : l' = i
  · subst h
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_of_ne h, h]

/- English proof (translation)
Take `⟨q, hq⟩` from `Function.ne_iff.1 h0`. Use `set r := plE M k q with hr`. Use `set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA`. Use `set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'`. Establish `hdet : A'.det ≠ 0` using `hq`.

Establish `hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c)`. Use extensionality with `i s`. Rewrite using `[hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]`. Both sides reduce to the same expression. Establish `hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c)`.

Use `congrArg (fun X => A' * X) hadj` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this`. Simplify `this` using `[Matrix.smul_mul]`. Establish `hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j`. Use function extensionality and compare the values at `s`.

Establish `h2` using `congrFun (congrFun hC l) s`. Simplify using `only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrow]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem mem_span_of_plk_eq_smul (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K)
    (h0 : plk c' id ≠ 0) (h : plk c' id = a • plk c id) (l : Fin k) :
    c' l ∈ Submodule.span K (Set.range c) := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  set r := plE M k q with hr
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA
  set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'
  have hdet : A'.det ≠ 0 := hq
  have hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c) := by
    ext i s
    rw [hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]
    rfl
  have hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c) := by
    have := congrArg (fun X => A' * X) hadj
    simp only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this
    simpa [Matrix.smul_mul] using this
  have hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j := by
    funext s
    have h2 := congrFun (congrFun hC l) s
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.FlagEmb
