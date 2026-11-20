import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem posEx : PosEx := by
  intro F E _ _ _ _ _ σ hc δ hδ hs
  have key : ∀ w : InfinitePlace F, ∃ t : EmbOver E w, ∃ c : ℝ, 0 < c ∧ Complex.I * t.1 δ = c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    have hconj : ∀ (t : E →+* ℂ) (x : E), t (σ x) = star (t x) := hc.2.2.2
    set z : ℂ := τ.1 δ with hz
    have hstar : star z = -z := by
      rw [hz, ← hconj, hs, map_neg]
    have hre : z.re = 0 := by
      have := congrArg Complex.re hstar
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have hz0 : z ≠ 0 := by
      rw [hz]
      exact (map_ne_zero τ.1).2 hδ
    have him : z.im ≠ 0 := fun h => hz0 (Complex.ext hre h)
    have hI : Complex.I * z = ((-z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨τ, -z.im, by linarith, hI⟩
    · refine ⟨⟨τ.1.comp (σ : E →+* E), ?_⟩, z.im, h, ?_⟩
      · refine Eq.trans ?_ τ.2
        ext x
        simp
      · have : (τ.1.comp (σ : E →+* E)) δ = -z := by
          simp [hs, hz]
        rw [this, mul_neg, hI]
        simp
  choose emb hemb using key
  exact ⟨emb, hemb⟩

end UpperTheory.Gal.TP.Skew

end
