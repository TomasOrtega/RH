import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Establish `hlift : ∀ i, ∃ y ∈ H, π y = ∑ j, P i j • v j`. Introduce `i`. Establish `hmem : (∑ j, P i j • v j) ∈ H.map (π.restrictScalars R)`. Rewrite using `[hmap]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Take `⟨y, hy, e⟩` from `hmem`. Conclude with `⟨y, hy, e⟩`. Use `choose h hH hπh using hlift`. Establish `hT : ∀ i, ∃ t : Fin (p + q) → Ω, ∑ k, t k • u k = h i` using `fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hHu _ (hH i))`. Use `choose T hT using hT`.

Establish `hTP : ∀ i j, T i (Fin.castAdd q j) = P i j`. Introduce `i`. Establish `e : ∑ j, T i (Fin.castAdd q j) • v j = ∑ j, P i j • v j`. Rewrite using `[← hπh i, ← hT i, map_sum, Fin.sum_univ_add]`. Simplify using `[hπ1, hπ2]`.

Establish `e2 : ∑ j, (T i (Fin.castAdd q j) - P i j) • v j = 0`. Simplify using `[sub_smul, Finset.sum_sub_distrib, e]`. Introduce `j`. Conclude with `sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e2 j)`. Set `T2 : Matrix (Fin p) (Fin q) Ω` to `fun i k => T i (Fin.natAdd p k)`.

Set `A : Matrix (Fin (p + q)) (Fin (p + q)) Ω` to `Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P T2 0 C)`. Establish `hA11 : ∀ i j, A (Fin.castAdd q i) (Fin.castAdd q j) = P i j`. Introduce `i j`. Simplify using `[A, Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hA12 : ∀ i j, A (Fin.castAdd q i) (Fin.natAdd p j) = T i (Fin.natAdd p j)`.

Introduce `i j`. Express the relevant statement in the definitionally equal form `A (Fin.castAdd q i) (Fin.natAdd p j) = T2 i j`. Simplify using `[A, Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hA21 : ∀ i j, A (Fin.natAdd p i) (Fin.castAdd q j) = 0`. Introduce `i j`.

Simplify using `[A, Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hA22 : ∀ i j, A (Fin.natAdd p i) (Fin.natAdd p j) = C i j`. Introduce `i j`. Simplify using `[A, Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hdet : A.det = P.det * C.det`.

Simplify using `only [A, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`. Establish `hw1 : ∀ i, ∑ j, A (Fin.castAdd q i) j • u j = h i`. Introduce `i`. Rewrite using `[← hT i, Fin.sum_univ_add, Fin.sum_univ_add]`. Simplify using `only [hA11, hA12, hTP]`.

Establish `hw2 : ∀ i, ∑ j, A (Fin.natAdd p i) j • u j = ∑ k, C i k • u (Fin.natAdd p k)`. Introduce `i`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [hA21, hA22, zero_smul, Finset.sum_const_zero, zero_add]`. Use `⟨A, hdet, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `hc' : ∑ j, (∑ i, c i * A i j) • u j = 0`. Rewrite using `[← hc]`. Simplify using `only [Finset.smul_sum, Finset.sum_smul, mul_smul]`.

Conclude with `Finset.sum_comm`. Establish `hz` using `Fintype.linearIndependent_iff.1 hu _ hc'`. Establish `hvm : Matrix.vecMul c A = 0`. Use function extensionality and compare the values at `j`. Simplify `hz j` using `[Matrix.vecMul, dotProduct]`.

Establish `hdet0 : A.det ≠ 0` using `by rw [hdet]; exact mul_ne_zero hP hC`. Use `Matrix.eq_zero_of_vecMul_eq_zero hdet0 hvm` as an intermediate fact. Introduce `i`. Conclude with `congrFun this i`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `y hy`. Establish `hmem : π y ∈ Submodule.span R (Set.range fun i => ∑ j, P i j • v j)`. Rewrite using `[← hmap]`. Conclude with `⟨y, hy, rfl⟩`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hmem`.

Use `set S := Submodule.span R (Set.range fun i => ∑ j, A i j • u j) with hS`. Establish `hhS : ∀ i, h i ∈ S` using `fun i => by`. Rewrite using `[← hw1 i]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hCS : Submodule.span R (Set.range fun j => ∑ k, C j k • u (Fin.natAdd p k)) ≤ S`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `hw2 j` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[← this]`.

Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Establish `hsumH : ∑ i, r i • h i ∈ H` using `Submodule.sum_mem _ fun i _ => H.smul_mem _ (hH i)`. Establish `hsumS : ∑ i, r i • h i ∈ S` using `Submodule.sum_mem _ fun i _ => S.smul_mem _ (hhS i)`. Establish `hdiff : y - ∑ i, r i • h i ∈ H` using `H.sub_mem hy hsumH`. Establish `hπd : π (y - ∑ i, r i • h i) = 0`.

Establish `e : π (∑ i, r i • h i) = ∑ i, r i • ∑ j, P i j • v j`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hπh i, Subring.smul_def, Subring.smul_def, map_smul]`. Rewrite using `[map_sub, e, hr, sub_self]`.

Use `hCS (hker _ hdiff hπd)` as an intermediate fact. Simplify using `using S.add_mem this hsumS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations.

Simplify using `only [SetLike.mem_coe]`. Rewrite using `[hw1]`. Conclude with `hH i`. Simplify using `only [SetLike.mem_coe]`. Rewrite using `[hw2]`.

Conclude with `hCH i`.
-/
theorem ext_frame_of_quotient_kernel (Ω M V : Type) [Field Ω] [AddCommGroup M] [Module Ω M]
    [AddCommGroup V] [Module Ω V] (R : Subring Ω) (H : Submodule R M) (π : M →ₗ[Ω] V) (p q : ℕ)
    (u : Fin (p + q) → M) (v : Fin p → V) (P : Matrix (Fin p) (Fin p) Ω)
    (C : Matrix (Fin q) (Fin q) Ω)
    (hu : LinearIndependent Ω u) (hv : LinearIndependent Ω v)
    (hHu : ∀ y ∈ H, y ∈ Submodule.span Ω (Set.range u))
    (hπ1 : ∀ i, π (u (Fin.castAdd q i)) = v i) (hπ2 : ∀ j, π (u (Fin.natAdd p j)) = 0)
    (hP : P.det ≠ 0) (hC : C.det ≠ 0)
    (hmap : H.map (π.restrictScalars R) = Submodule.span R (Set.range fun i => ∑ j, P i j • v j))
    (hCH : ∀ j, ∑ k, C j k • u (Fin.natAdd p k) ∈ H)
    (hker : ∀ y ∈ H, π y = 0 →
      y ∈ Submodule.span R (Set.range fun j => ∑ k, C j k • u (Fin.natAdd p k))) :
    ∃ A : Matrix (Fin (p + q)) (Fin (p + q)) Ω, A.det = P.det * C.det ∧
      LinearIndependent Ω (fun i => ∑ j, A i j • u j) ∧
      H = Submodule.span R (Set.range fun i => ∑ j, A i j • u j) := by
  classical
  have hlift : ∀ i, ∃ y ∈ H, π y = ∑ j, P i j • v j := by
    intro i
    have hmem : (∑ j, P i j • v j) ∈ H.map (π.restrictScalars R) := by
      rw [hmap]; exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hmem
    exact ⟨y, hy, e⟩
  choose h hH hπh using hlift
  have hT : ∀ i, ∃ t : Fin (p + q) → Ω, ∑ k, t k • u k = h i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hHu _ (hH i))
  choose T hT using hT
  have hTP : ∀ i j, T i (Fin.castAdd q j) = P i j := by
    intro i
    have e : ∑ j, T i (Fin.castAdd q j) • v j = ∑ j, P i j • v j := by
      rw [← hπh i, ← hT i, map_sum, Fin.sum_univ_add]
      simp [hπ1, hπ2]
    have e2 : ∑ j, (T i (Fin.castAdd q j) - P i j) • v j = 0 := by
      simp [sub_smul, Finset.sum_sub_distrib, e]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv _ e2 j)
  let T2 : Matrix (Fin p) (Fin q) Ω := fun i k => T i (Fin.natAdd p k)
  let A : Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P T2 0 C)
  have hA11 : ∀ i j, A (Fin.castAdd q i) (Fin.castAdd q j) = P i j := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA12 : ∀ i j, A (Fin.castAdd q i) (Fin.natAdd p j) = T i (Fin.natAdd p j) := by
    intro i j
    change A (Fin.castAdd q i) (Fin.natAdd p j) = T2 i j
    simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA21 : ∀ i j, A (Fin.natAdd p i) (Fin.castAdd q j) = 0 := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hA22 : ∀ i j, A (Fin.natAdd p i) (Fin.natAdd p j) = C i j := by
    intro i j; simp [A, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdet : A.det = P.det * C.det := by
    simp only [A, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have hw1 : ∀ i, ∑ j, A (Fin.castAdd q i) j • u j = h i := by
    intro i
    rw [← hT i, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [hA11, hA12, hTP]
  have hw2 : ∀ i, ∑ j, A (Fin.natAdd p i) j • u j = ∑ k, C i k • u (Fin.natAdd p k) := by
    intro i
    rw [Fin.sum_univ_add]
    simp only [hA21, hA22, zero_smul, Finset.sum_const_zero, zero_add]
  refine ⟨A, hdet, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ j, (∑ i, c i * A i j) • u j = 0 := by
      rw [← hc]
      simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    have hz := Fintype.linearIndependent_iff.1 hu _ hc'
    have hvm : Matrix.vecMul c A = 0 := by
      funext j
      simpa [Matrix.vecMul, dotProduct] using hz j
    have hdet0 : A.det ≠ 0 := by rw [hdet]; exact mul_ne_zero hP hC
    have := Matrix.eq_zero_of_vecMul_eq_zero hdet0 hvm
    intro i
    exact congrFun this i
  · apply le_antisymm
    · intro y hy
      have hmem : π y ∈ Submodule.span R (Set.range fun i => ∑ j, P i j • v j) := by
        rw [← hmap]; exact ⟨y, hy, rfl⟩
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
      set S := Submodule.span R (Set.range fun i => ∑ j, A i j • u j) with hS
      have hhS : ∀ i, h i ∈ S := fun i => by
        rw [← hw1 i]; exact Submodule.subset_span ⟨_, rfl⟩
      have hCS : Submodule.span R (Set.range fun j => ∑ k, C j k • u (Fin.natAdd p k)) ≤ S := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have := hw2 j
        simp only at this ⊢
        rw [← this]; exact Submodule.subset_span ⟨_, rfl⟩
      have hsumH : ∑ i, r i • h i ∈ H := Submodule.sum_mem _ fun i _ => H.smul_mem _ (hH i)
      have hsumS : ∑ i, r i • h i ∈ S := Submodule.sum_mem _ fun i _ => S.smul_mem _ (hhS i)
      have hdiff : y - ∑ i, r i • h i ∈ H := H.sub_mem hy hsumH
      have hπd : π (y - ∑ i, r i • h i) = 0 := by
        have e : π (∑ i, r i • h i) = ∑ i, r i • ∑ j, P i j • v j := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hπh i, Subring.smul_def, Subring.smul_def, map_smul]
        rw [map_sub, e, hr, sub_self]
      have := hCS (hker _ hdiff hπd)
      simpa using S.add_mem this hsumS
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [SetLike.mem_coe]; rw [hw1]; exact hH i
      · simp only [SetLike.mem_coe]; rw [hw2]; exact hCH i

end GlobalTheory.CompanionTheory.Ggeo
