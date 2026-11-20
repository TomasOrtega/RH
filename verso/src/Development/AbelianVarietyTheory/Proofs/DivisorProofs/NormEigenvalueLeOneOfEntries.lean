import Mathlib

namespace GlobalTheory.EigenvalueNormAtMostOne

/- English proof (translation)
Take `⟨k, hk⟩` from `Function.ne_iff.mp hc`. Take `⟨i, -, hi⟩` from `Finset.exists_max_image Finset.univ (fun j => ‖c j‖) ⟨k, Finset.mem_univ k⟩`. Establish `hpos : 0 < ‖c i‖` using `lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi k (Finset.mem_univ k))`. Establish `hrow : ∑ j, A i j * c j = μ * c i`. Use `congrFun h i` as an intermediate fact.

Simplify `this` using `[Matrix.mulVec, dotProduct]`. Establish `hle : ‖∑ j, A i j * c j‖ ≤ ‖c i‖`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hle` using `[hrow, norm_mul]`. Conclude with `le_of_mul_le_mul_right (by rwa [one_mul]) hpos`.
-/
theorem norm_eigenvalue_le_one_of_entries {K : Type} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (c : Fin n → K) (μ : K) (hc : c ≠ 0) (h : A.mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖)
    ⟨k, Finset.mem_univ k⟩
  have hpos : 0 < ‖c i‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi k (Finset.mem_univ k))
  have hrow : ∑ j, A i j * c j = μ * c i := by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  have hle : ‖∑ j, A i j * c j‖ ≤ ‖c i‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j hj
    rw [norm_mul]
    calc ‖A i j‖ * ‖c j‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul (hA i j) (hi j hj) (norm_nonneg _) zero_le_one
      _ = ‖c i‖ := one_mul _
  rw [hrow, norm_mul] at hle
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

/- English proof (translation)
Introduce `l _ O _ emb hemb n N c μ hc h`. Conclude with `norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h`.
-/
theorem norm_eigenvalue_le_one :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (O : Type) [inst_1 : CommRing O]
      (emb : O →+* PadicAlgCl l), (∀ (a : O), ‖(emb : O → PadicAlgCl l) a‖ ≤ (1 : ℝ)) →
      ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l) (μ : PadicAlgCl l),
        c ≠ (0 : Fin n → PadicAlgCl l) →
        Matrix.mulVec (Matrix.map N (⇑emb : O → PadicAlgCl l)) c = μ • c → ‖μ‖ ≤ (1 : ℝ) := by
  intro l _ O _ emb hemb n N c μ hc h
  exact norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h

end GlobalTheory.EigenvalueNormAtMostOne
