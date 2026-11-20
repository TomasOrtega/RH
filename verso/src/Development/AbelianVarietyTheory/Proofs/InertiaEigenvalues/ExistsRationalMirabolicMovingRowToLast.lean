import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Both sides reduce to the same expression. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem mir_exists_row : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a →
    ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧
      ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  intro E _ _ a m hma ξ hξ
  classical
  set mm : Fin a := ⟨m, by omega⟩ with hmm
  set c : Fin a := ⟨m + 1, hma⟩ with hc
  let v : Fin a → E := fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0
  have hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t := by
    intro t
    have h1 := t.2
    have hle : (t.1.1 : ℕ) ≤ m := by omega
    simp only [v, dif_pos hle]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp [hc]; omega
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hξ
  set i₀ : Fin a := t₀.1.1 with hi₀
  have hi₀m : (i₀ : ℕ) ≤ m := by have := t₀.2; omega
  have hvi₀ : v i₀ ≠ 0 := by rw [hi₀, hv]; exact ht₀
  let M : Matrix (Fin a) (Fin a) E := Matrix.of fun i k =>
    if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ j, (M *ᵥ x) j = 0 := fun j => by rw [hx]; rfl
    have hoff : ∀ j, j ≠ i₀ → x j = 0 := by
      intro j hj
      by_cases hjm : j = mm
      · have hi₀ne : i₀ ≠ mm := hjm ▸ Ne.symm hj
        have := hrow i₀
        simpa [M, Matrix.mulVec, dotProduct, hi₀ne, hjm] using this
      · have := hrow j
        simpa [M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply] using this
    apply hx0
    funext j
    by_cases hj : j = i₀
    · subst hj
      have := hrow mm
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)] at this
      exact (mul_eq_zero.1 this).resolve_left hvi₀
    · exact hoff j hj
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hu.unit, ?_, ?_⟩
  · intro i k hik
    rw [IsUnit.unit_spec]
    simp only [M, Matrix.of_apply]
    rcases hik with hi | hk
    · have h1 : i ≠ mm := fun e => by rw [e] at hi; simp [hmm] at hi
      have h2 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      simp [h1, h2]
    · have h1 : k ≠ mm := fun e => by rw [e] at hk; simp [hmm] at hk
      have h2 : k ≠ i₀ := fun e => by rw [e] at hk; omega
      split_ifs with e1 e2
      · subst e1
        simp only [v, Matrix.one_apply, h1.symm, if_false]
        rw [dif_neg (by omega)]
      · simp [e2, Matrix.one_apply, Ne.symm h2]
      · rfl
  · intro t
    rw [IsUnit.unit_spec]
    have hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm := ⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Finset.sum_eq_single s₀]
    · simp only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]
      exact hv t
    · intro s _ hs
      have : ¬ ((s.1.1 : ℕ) + 1 = m + 1) := by
        intro e
        apply hs
        apply Subtype.ext
        have h1 := s.2; have h2 := s₀.2
        apply Prod.ext
        · apply Fin.ext; rw [hs₀]; simp [hmm]; omega
        · apply Fin.ext; omega
      simp only [eLast, if_neg this, zero_mul]
    · simp

end GlobalTheory.CuspGeneric
