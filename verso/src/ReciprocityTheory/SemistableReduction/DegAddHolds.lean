import ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
import ReciprocityTheory.SemistableReduction.EmbMatMulVecInjective

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem degAdd_holds : DegAddStatement := by
  intro K _ _ r k m H L b c hH hL hb hc hlin hspan
  obtain ⟨hbi, -, hdis⟩ := DegAdd.indep_parts hlin
  have hidx := DegAdd.index_split L b c hb hc hdis
  have hne := DegAdd.relIndex_ne_zero_of_fg L hL (Fin.append b c) hspan
  rw [hidx] at hne
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hs : ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ (Fin.append b c)).det.re =
      ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re +
        ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => DegAdd.log_det_gram_append (H σ) σ b c (hH σ) hbi hlin
  unfold latDeg quotDeg
  rw [hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr h1) (Nat.cast_ne_zero.mpr h2), hs]
  ring

end ReciprocityTheory.MultiplicativeHeights
