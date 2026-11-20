import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

namespace GlobalTheory.IntwLeftMul

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem leftMul_coord {G : Type} {m : ℕ} (A : G → Matrix (Fin m) (Fin m) ℂ) (k : G)
    (v : EuclideanSpace ℂ (Fin (m * m))) (i j : Fin m) :
    (leftMul A k v) (finProdFinEquiv (i, j)) = ∑ l, A k i l * v (finProdFinEquiv (l, j)) := by
  unfold leftMul
  rw [Matrix.ofLp_toEuclideanCLM]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply]

noncomputable def colMap {V : Type} [AddCommGroup V] [Module ℂ V] (D : Submodule ℂ V) {m : ℕ}
    (b : Fin m → V) (hbD : ∀ i, b i ∈ D) (j : Fin m) :
    EuclideanSpace ℂ (Fin (m * m)) →ₗ[ℂ] D where
  toFun v := ⟨∑ i, v (finProdFinEquiv (i, j)) • b i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbD i)⟩
  map_add' v w := by
    ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext; simp [Finset.smul_sum, smul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colMap_val {V : Type} [AddCommGroup V] [Module ℂ V] (D : Submodule ℂ V) {m : ℕ}
    (b : Fin m → V) (hbD : ∀ i, b i ∈ D) (j : Fin m) (v : EuclideanSpace ℂ (Fin (m * m))) :
    ((colMap D b hbD j v : D) : V) = ∑ i, v (finProdFinEquiv (i, j)) • b i := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem exists_intertwiner (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (m : ℕ) (b : Fin m → V)
    (A : G → Matrix (Fin m) (Fin m) ℂ) (hbD : ∀ i, b i ∈ D) (f : Fin m → (D →ₗ[ℂ] D)) :
    (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) →
    (∀ j, ∀ k ∈ K, ∀ u v : D, (v : V) = ρ k u → (f j v : V) = ρ k (f j u)) →
    ∃ T : EuclideanSpace ℂ (Fin (m * m)) →ₗ[ℂ] V,
      (∀ k ∈ K, ∀ v, T (leftMul A k v) = ρ k (T v)) ∧
      ∑ j, ((f j ⟨b j, hbD j⟩ : D) : V) ∈ LinearMap.range T := by
  intro hA hf
  refine ⟨∑ j, D.subtype ∘ₗ (f j) ∘ₗ colMap D b hbD j, ?_, ?_⟩
  · intro k hk v
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Submodule.coe_subtype]
    apply hf j k hk
    rw [colMap_val, colMap_val]
    simp only [leftMul_coord, Finset.sum_smul, map_sum, map_smul, hA k hk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · refine ⟨WithLp.toLp 2 (fun x => if (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm x).2 then 1 else 0), ?_⟩
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ext
    rw [colMap_val]
    simp [Finset.sum_ite_eq']

end GlobalTheory.IntwLeftMul
