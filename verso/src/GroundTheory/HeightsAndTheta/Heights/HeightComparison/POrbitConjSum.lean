import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSumLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G OrbitConjSum

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem OrbitConjSum.proof : OrbitConjSum.Statement := by
  intro ι _ _ n x g hx hg
  classical
  obtain ⟨c, hc⟩ := exists_chart hx
  let L := ratioField x c
  have hΦ : Function.Surjective (conjPt x hx) := exists_conjPt_eq x hx c hc
  have : Finite (projPts (ι := blockIdx n) (orbitIdeal x)) := Finite.of_surjective _ hΦ
  let _ : Fintype (projPts (ι := blockIdx n) (orbitIdeal x)) := Fintype.ofFinite _

  let G : projPts (ι := blockIdx n) (orbitIdeal x) → ℝ := Quot.lift (fun z ↦ g z.1) (by
    rintro z z' ⟨a, ha, e⟩
    simp only [e]
    exact (hg a z ha z.2).symm)
  have hG : ∀ q, g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) = G q := fun q ↦ by
    conv_rhs => rw [← Quot.out_eq q]

  have hfib : ∀ q, (Finset.univ.filter fun σ ↦ conjPt x hx σ = q).card =
      Module.finrank L (coordField x) := by
    intro q
    obtain ⟨σ₀, rfl⟩ := hΦ q
    rw [← card_embeddings_restrict (K := L) (L := coordField x)
      (σ₀.comp (algebraMap L (coordField x)))]
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conjPt_eq_iff x hx c hc, restrict_eq_iff]
  have hsum : ∀ F : projPts (ι := blockIdx n) (orbitIdeal x) → ℝ,
      ∑ σ : coordField x →+* ℂ, F (conjPt x hx σ) =
        Module.finrank L (coordField x) * ∑ q, F q := by
    intro F
    rw [← Finset.sum_fiberwise' Finset.univ (conjPt x hx), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Finset.sum_const, hfib, nsmul_eq_mul]
  have hdeg : (Module.finrank ℚ (coordField x) : ℝ) = Module.finrank L (coordField x) *
      Fintype.card (projPts (ι := blockIdx n) (orbitIdeal x)) := by
    have h := hsum fun _ ↦ 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    rw [NumberField.Embeddings.card] at h
    exact h
  rw [degC_eq_card_projPts, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl fun q _ ↦ hG q, hdeg]
  rw [show ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
    ∑ σ : coordField x →+* ℂ, G (conjPt x hx σ) from rfl, hsum G]
  ring

end

end GroundTheory.Heights₂.Heights
