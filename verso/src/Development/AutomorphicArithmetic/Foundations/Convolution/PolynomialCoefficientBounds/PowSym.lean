import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.FX.esymm_pow :
    ∀ (n f : ℕ) (i : Fin n), ∃ g : MvPolynomial (Fin n) ℂ, aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) g = aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f) (esymm (Fin n) ℂ (i + 1)) := by
  intro n f i
  have hs : (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)
      (esymm (Fin n) ℂ (i + 1))).IsSymmetric := by
    intro e
    have h : (rename e).comp (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f))
        = (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)).comp
            (rename e : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) := by
      apply MvPolynomial.algHom_ext
      intro r
      simp
    have h2 := DFunLike.congr_fun h (esymm (Fin n) ℂ (i + 1))
    simp only [AlgHom.comp_apply] at h2
    rw [h2, esymm_isSymmetric (Fin n) ℂ (i + 1) e]
  obtain ⟨g, hg⟩ := esymmAlgHom_surjective (σ := Fin n) ℂ (n := n) (by simp)
    ⟨_, (mem_symmetricSubalgebra _).2 hs⟩
  refine ⟨g, ?_⟩
  have := congrArg Subtype.val hg
  rw [esymmAlgHom_apply] at this
  exact this
