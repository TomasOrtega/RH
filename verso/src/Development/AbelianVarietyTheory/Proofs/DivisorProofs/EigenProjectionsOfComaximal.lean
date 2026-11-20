import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem eigenProjections_of_comaximal :
    ∀ (R F : Type) [CommRing R] [CommRing F] (a : ℕ) (t : Fin a → (F →+* R)),
      (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) →
      ∃ e : Fin a → R ⊗[ℤ] F, ∀ (M : Type) [AddCommGroup M] (Θ : R ⊗[ℤ] F →+* AddMonoid.End M)
        (i l : Fin a) (m : M), (∀ c : F, Θ (1 ⊗ₜ c) m = Θ (t l c ⊗ₜ 1) m) →
          Θ (e i) m = if i = l then m else 0 := by
  intro R F _ _ a t ht
  have hf : ∀ i j : Fin a, ∃ f : F →₀ R, i ≠ j → (f.sum fun c r => r * (t i c - t j c)) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : R) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [ht i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      exact ⟨f, fun _ => by simpa [smul_eq_mul] using hf⟩
  choose f hf using hf
  let χ : Fin a → (R ⊗[ℤ] F →ₐ[ℤ] R) := fun l =>
    Algebra.TensorProduct.productMap (AlgHom.id ℤ R) (t l).toIntAlgHom
  have hχ : ∀ l r c, χ l (r ⊗ₜ c) = r * t l c := by
    intro l r c; simp [χ, Algebra.TensorProduct.productMap_apply_tmul]
  refine ⟨fun i => ∏ j, if j = i then 1 else
    (f i j).sum fun c r => (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c - t j c ⊗ₜ (1:F)), ?_⟩
  intro M _ Θ i l m hm
  have key : ∀ z, Θ z m = Θ (χ l z ⊗ₜ (1:F)) m := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      have e1 : (r ⊗ₜ c : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * ((1:R) ⊗ₜ c) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : ((r * t l c) ⊗ₜ (1:F) : R ⊗[ℤ] F) = (r ⊗ₜ (1:F)) * (t l c ⊗ₜ (1:F)) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hχ, e1, e2, map_mul, map_mul]
      change Θ (r ⊗ₜ 1) (Θ (1 ⊗ₜ c) m) = Θ (r ⊗ₜ 1) (Θ (t l c ⊗ₜ 1) m)
      rw [hm c]
    | add x y hx hy =>
      rw [map_add, map_add, TensorProduct.add_tmul, map_add]
      change Θ x m + Θ y m = Θ (χ l x ⊗ₜ 1) m + Θ (χ l y ⊗ₜ 1) m
      rw [hx, hy]
  rw [key, map_prod]
  split_ifs with hil
  · subst hil
    rw [Finset.prod_eq_one]
    · rw [← Algebra.TensorProduct.one_def, map_one]; rfl
    intro j _
    split_ifs with hji
    · exact map_one _
    · unfold Finsupp.sum
      rw [map_sum]
      have := hf i j (Ne.symm hji)
      unfold Finsupp.sum at this
      refine Eq.trans ?_ this
      apply Finset.sum_congr rfl
      intro c _
      rw [map_mul, map_sub, hχ, hχ, hχ]
      simp
  · rw [Finset.prod_eq_zero (Finset.mem_univ l)]
    · rw [TensorProduct.zero_tmul, map_zero]; rfl
    rw [if_neg (Ne.symm hil)]
    unfold Finsupp.sum
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c _
    rw [map_mul, map_sub, hχ, hχ, hχ]
    simp

end GlobalTheory
