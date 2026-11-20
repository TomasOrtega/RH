import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.InjectiveOfInjectiveCompAevalOfTrdegLe

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Put the expressions in a common number system so they can be compared.

Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem det_ne_zero_of_generic_linear_forms_vanish :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) (g N : ℕ)
    (T : Fin g × Fin N → K) (e : Fin N → K) (D : Fin g → Fin N → K),
    AlgebraicIndependent k T → Algebra.trdeg k F ≤ g → (∀ j, e j ∈ F) → (∀ a j, D a j ∈ F) →
    (∃ j, e j ≠ 0) →
    (∃ c : Fin g → Fin N → K, (∀ i, ∑ j, c i j * e j = 0) ∧
      (Matrix.of fun i a => ∑ j, c i j * D a j).det ≠ 0) →
    (∀ i, ∑ j, T (i, j) * e j = 0) → (Matrix.of fun i a => ∑ j, T (i, j) * D a j).det ≠ 0 := by
  intro k K _ _ _ F g N T e D hT hF he hD ⟨j0, hj0⟩ ⟨c, hc, hcd⟩ hTe
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by have := j0.pos; omega⟩
  let η : Fin (M + 1) → F := fun j => ⟨e j / e j0, F.div_mem (he j) (he j0)⟩
  let D' : Fin g → Fin (M + 1) → F := fun a j => ⟨D a j, hD a j⟩
  let b : Fin g × Fin (M + 1) → MvPolynomial (Fin g × Fin M) F := fun p =>
    Fin.insertNth (α := fun _ => MvPolynomial (Fin g × Fin M) F) j0
      (-∑ l : Fin M, X (p.1, l) * C (η (j0.succAbove l))) (fun l => X (p.1, l)) p.2
  let χ : (Fin g × Fin (M + 1) → K) → (MvPolynomial (Fin g × Fin M) F →ₐ[F] K) := fun v =>
    aeval fun q => v (q.1, j0.succAbove q.2)
  have hb : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      ∀ p, χ v (b p) = v p := by
    rintro v hv ⟨i, j⟩
    refine Fin.succAboveCases j0 ?_ (fun l => ?_) j
    · have h1 := hv i
      rw [Fin.sum_univ_succAbove _ j0] at h1
      have h2 : v (i, j0) =
          -∑ l : Fin M, v (i, j0.succAbove l) * (e (j0.succAbove l) / e j0) := by
        simp only [← mul_div_assoc, ← Finset.sum_div]
        field_simp
        linear_combination h1
      rw [h2]
      simp [b, χ, η]
    · simp [b, χ]
  let Δ : MvPolynomial (Fin g × Fin M) F :=
    (Matrix.of fun i a => ∑ j, b (i, j) * C (D' a j)).det
  have hΔ : ∀ v : Fin g × Fin (M + 1) → K, (∀ i, ∑ j, v (i, j) * e j = 0) →
      χ v Δ = (Matrix.of fun i a => ∑ j, v (i, j) * D a j).det := by
    intro v hv
    rw [AlgHom.map_det]
    congr 1
    ext i a
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      hb v hv]
    simp [χ, D']
  have hΔ0 : Δ ≠ 0 := by
    intro h
    apply hcd
    rw [← hΔ (fun p => c p.1 p.2) hc, h, map_zero]
  have htr : Algebra.trdeg k (MvPolynomial (Fin g × Fin M) F) ≤
      Cardinal.mk (Fin g × Fin (M + 1)) := by
    have : FaithfulSMul F (MvPolynomial (Fin g × Fin M) F) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (MvPolynomial.C_injective _ _)
    rw [← trdeg_add_eq k F, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype, Cardinal.mk_fintype]
    refine (add_le_add_left hF _).trans ?_
    norm_cast
    simp only [Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  have hχ : Function.Injective (χ T).toRingHom := by
    refine injective_of_injective_comp_aeval_of_trdeg_le (k := k) b htr _ ?_
    have : (fun q : MvPolynomial (Fin g × Fin (M + 1)) k => (χ T).toRingHom (aeval b q)) =
        aeval T := by
      have h3 : ((χ T).restrictScalars k).comp (aeval b) = aeval T := by
        apply MvPolynomial.algHom_ext
        intro p
        simp [hb T hTe]
      funext q
      exact DFunLike.congr_fun h3 q
    rw [this]
    exact hT
  rw [← hΔ T hTe]
  intro h
  exact hΔ0 (hχ (by simpa using h))

end GlobalTheory
