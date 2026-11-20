import Mathlib

open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `n f i`. Establish `hs : (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f) (esymm (Fin n) ℂ (i + 1))).IsSymmetric`. Introduce `e`. Establish `h : (rename e).comp (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)) = (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)).comp (rename e : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `r`. Simplify using the standard rewrite rules. Establish `h2` using `DFunLike.congr_fun h (esymm (Fin n) ℂ (i + 1))`. Simplify using `only [AlgHom.comp_apply] at h2`. Rewrite using `[h2, esymm_isSymmetric (Fin n) ℂ (i + 1) e]`.

Take `⟨g, hg⟩` from `esymmAlgHom_surjective (σ := Fin n) ℂ (n := n) (by simp) ⟨_, (mem_symmetricSubalgebra _).2 hs⟩`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hg` as an intermediate fact. Rewrite `this` using `[esymmAlgHom_apply]`. Conclude with `this`.
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
