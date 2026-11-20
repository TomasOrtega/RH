import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem evC_conj {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    evC (fun p => (starRingEnd ℂ) (z p)) g = (starRingEnd ℂ) (evC z g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, Polynomial.map_add, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ptOver_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ),
    PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  intro K _ ι _ Ω _ F _ _ y φ σ z h
  obtain ⟨⟨hne, hvan⟩, hrel⟩ := h
  refine ⟨⟨fun k => ?_, fun f hf => ?_⟩, fun a d g h' hg hh e => ?_⟩
  · obtain ⟨i, hi⟩ := hne k
    exact ⟨i, by simpa using hi⟩
  · have := evC_conj z f
    have h0 : evC z f = 0 := hvan f hf
    rw [h0, map_zero] at this
    exact this
  · rw [evC_conj, evC_conj, hrel a d g h' hg hh e, map_mul, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CompanionTheory.Ar.Flat
