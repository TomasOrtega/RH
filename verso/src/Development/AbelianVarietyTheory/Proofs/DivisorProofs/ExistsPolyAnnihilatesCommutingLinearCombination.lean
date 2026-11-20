import Mathlib

noncomputable section

open Polynomial

namespace GlobalTheory.CommutingPoly

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  intro M _ _ ι _ A hc c P hP
  classical
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := Algebra.adjoinCommRingOfComm ℂ
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hc i j)
  let S := Algebra.adjoin ℂ (Set.range A)
  let I : Ideal S :=
    { carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0}
      add_mem' := by
        intro a b ha hb v hv
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha v hv, hb v hv]
      zero_mem' := by intro v _; simp
      smul_mem' := by
        intro a b hb v hv
        show ((a * b : S) : Module.End ℂ M) v = 0
        rw [Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }
  have hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0 :=
    fun a => Iff.rfl
  let t : ι → S := fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let q : S →ₐ[ℂ] S ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hint : ∀ i, IsIntegral ℂ (q (t i)) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩
    rw [aeval_algHom_apply]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    rw [hI]
    intro v hv
    rw [aeval_subalgebra_coe]
    exact hv i
  have hs : IsIntegral ℂ (q (∑ i, c i • t i)) := by
    rw [map_sum]
    exact IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)
  obtain ⟨p, hpm, hp⟩ := hs
  refine ⟨p, hpm.ne_zero, fun v hv => ?_⟩
  have hq : q (aeval (∑ i, c i • t i) p) = 0 := by
    rw [← aeval_algHom_apply, aeval_def]
    exact hp
  have hmem : aeval (∑ i, c i • t i) p ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have h := (hI _).mp hmem v hv
  rw [aeval_subalgebra_coe] at h
  have hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i := by
    rw [show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]
    simp [t]
  rw [hsum] at h
  exact h

end GlobalTheory.CommutingPoly
