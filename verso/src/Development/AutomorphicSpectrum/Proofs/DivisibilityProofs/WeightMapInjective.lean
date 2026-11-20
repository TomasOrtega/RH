import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem aeval_tail_gapX {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) :
    (aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)))
      (PB.gapX p) = X p := by
  obtain ⟨τ, i⟩ := p
  simp only [PB.gapX, map_sub, aeval_X]
  split_ifs with h
  · rw [aeval_X]
    have hI : Finset.Ici i = insert i (Finset.Ici (⟨(i : ℕ) + 1, h⟩ : Fin N)) := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [hI, Finset.sum_insert (by simp [Fin.le_def])]
    ring
  · have hI : Finset.Ici i = {i} := by
      ext s
      have := s.2
      simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    rw [map_zero, sub_zero, hI, Finset.sum_singleton]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toWt_leftInverse_injective (Ψ : Type) (N : ℕ) :
    Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := by
  set T : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval (fun q : Ψ × Fin N => ∑ s ∈ Finset.Ici q.2, (X (q.1, s) : MvPolynomial (Ψ × Fin N) ℝ)) with hT
  have hli : T.comp PB.toWt = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply, PB.toWt, aeval_X, hT]
    exact aeval_tail_gapX p
  intro a b hab
  have ha : T (PB.toWt a) = a := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  have hb : T (PB.toWt b) = b := by rw [← AlgHom.comp_apply, hli, AlgHom.id_apply]
  rw [← ha, ← hb, hab]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
