import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem adjugate_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ}
    (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (i j : Fin r) :
    P.adjugate i j ∈ R := by
  let P' : Matrix (Fin r) (Fin r) R := fun a b => ⟨P a b, hP a b⟩
  have hPP : P = (R.subtype).mapMatrix P' := by
    ext a b
    rfl
  rw [hPP, ← RingHom.map_adjugate]
  exact (P'.adjugate i j).2

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem linearIndependent_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {β : Fin r → E} (hβ : LinearIndependent Ω β) (P : Matrix (Fin r) (Fin r) Ω) (hd : P.det ≠ 0) :
    LinearIndependent Ω (fun k => ∑ a, P a k • β a) := by
  rw [Fintype.linearIndependent_iff] at hβ ⊢
  intro g hg
  have h1 : ∀ a, ∑ k, P a k * g k = 0 := by
    apply hβ
    refine Eq.trans ?_ hg
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have h2 : Matrix.mulVec P g = 0 := by
    funext a
    exact h1 a
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hd h2
  intro i
  rw [h3]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem span_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ}
    (β : Fin r → E) (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (hd : P.det ≠ 0)
    (hdi : P.det⁻¹ ∈ R) :
    Submodule.span R (Set.range fun k => ∑ a, P a k • β a) = Submodule.span R (Set.range β) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)
    refine sum_mem fun a _ => ?_
    exact Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro b
    show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)
    have hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b := fun a =>
      (Matrix.mul_apply).symm
    have hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b := by
      calc ∑ k, P.adjugate k b • ∑ a, P a k • β a
          = ∑ a, (∑ k, P a k * P.adjugate k b) • β a := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = ∑ a, (P * P.adjugate) a b • β a := by
            simp only [hm]
        _ = P.det • β b := by
            rw [Matrix.mul_adjugate]
            simp [Matrix.one_apply]
    have key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a := by
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [key]
    refine sum_mem fun k _ => ?_
    exact Submodule.smul_mem _
      (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R)
      (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isFrameAt_matrix_comb : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ)
    (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det →
    L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  intro X Ω _ ξ E _ _ L r β q P h1 h2 h3
  obtain ⟨hli, hspan⟩ := h1
  obtain ⟨hne, -, hinv⟩ := h3
  show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧
    L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)
  refine ⟨linearIndependent_matrix_comb hli P hne, ?_⟩
  rw [hspan]
  exact (span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm

end GlobalTheory.CompanionTheory.Ar.FlagBun
