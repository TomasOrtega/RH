import Mathlib
open scoped Topology

namespace GlobalTheory

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem differentiableOn_det_of_entries_frameCoord {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : ℕ} {U : Set X} (A : X → Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ a b, DifferentiableOn ℂ (fun s => A s a b) U) :
    DifferentiableOn ℂ (fun s => (A s).det) U := by
  simp only [Matrix.det_apply']
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.mul (differentiableOn_const _)
  have key : ∀ t : Finset (Fin g), DifferentiableOn ℂ (fun y => ∏ i ∈ t, A y (σ i) i) U := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (differentiableOn_const (1 : ℂ) : DifferentiableOn ℂ (fun _ : X => (1 : ℂ)) U)
    · intro a t ha ih
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact key _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem holomorphic_coordinates_in_holomorphic_frame : ∀ (n g : ℕ) (U : Set (Fin n → ℂ))
    (E F : (Fin n → ℂ) → Fin g → Fin g → ℂ), DifferentiableOn ℂ E U → DifferentiableOn ℂ F U →
    (∀ s ∈ U, (Matrix.of fun k i => E s i k).det ≠ 0) →
    ∃ τ : (Fin n → ℂ) → Fin g → Fin g → ℂ, DifferentiableOn ℂ τ U ∧
      ∀ s ∈ U, ∀ j, F s j = ∑ i, τ s i j • E s i := by
  intro n g U E F hE hF hdet
  let Emat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun s => Matrix.of fun k i => E s i k
  let Fmat : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun s => Matrix.of fun k j => F s j k
  refine ⟨fun s i j => ((Emat s)⁻¹ * Fmat s) i j, ?_, ?_⟩
  · have hEe : ∀ i k, DifferentiableOn ℂ (fun s => E s i k) U :=
      fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hE i) k
    have hFe : ∀ i k, DifferentiableOn ℂ (fun s => F s i k) U :=
      fun i k => differentiableOn_pi.1 (differentiableOn_pi.1 hF i) k
    have hdetD : DifferentiableOn ℂ (fun s => (Emat s).det) U :=
      differentiableOn_det_of_entries_frameCoord Emat (fun a b => by simpa [Emat] using hEe b a)
    have hadj : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s).adjugate a b) U := by
      intro a b
      simp only [Matrix.adjugate_apply]
      apply differentiableOn_det_of_entries_frameCoord
      intro r c
      by_cases hr : r = b
      · subst hr
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hr]
        simpa [Emat] using hEe c r
    have hinv : ∀ a b, DifferentiableOn ℂ (fun s => (Emat s)⁻¹ a b) U := by
      intro a b
      have hc : ∀ s ∈ U, ((Emat s).det)⁻¹ * (Emat s).adjugate a b = (Emat s)⁻¹ a b := by
        intro s _
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
        simp [Matrix.smul_apply]
      exact ((hdetD.inv (fun s hs => hdet s hs)).mul (hadj a b)).congr (fun s hs => (hc s hs).symm)
    rw [differentiableOn_pi]; intro i
    rw [differentiableOn_pi]; intro j
    simp only [Matrix.mul_apply]
    apply DifferentiableOn.fun_sum
    intro k _
    exact (hinv i k).mul (by simpa [Fmat] using hFe j k)
  · intro s hs j
    have h1 : Emat s * ((Emat s)⁻¹ * Fmat s) = Fmat s :=
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hdet s hs))
    funext k
    have h2 := congrFun (congrFun h1 k) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Emat, Fmat] at h2
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_apply, Emat, Fmat, Matrix.of_apply]
    ring

end GlobalTheory
