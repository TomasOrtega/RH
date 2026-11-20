import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ChosenHalf

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem isConjPl_unique (D : D7) {P w w' : PlE D.host} (h : IsConjPl D.host P w) (h' : IsConjPl D.host P w') :
    w = w' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem not_isConjPl_self (D : D7) {P : PlE D.host} (hs : IsSplitPl D.host P) : ¬ IsConjPl D.host P P := by
  intro hc
  obtain ⟨x, hx, hy⟩ := hs
  have hyx : ((RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x : 𝓞 D.host.E) : D.host.E) =
      D.host.conj (x : D.host.E) := rfl
  exact hy _ hyx ((hc x _ hyx).1 hx)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem overPl_unique (D : D7) {P : PlE D.host} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (h : NG.OverPl P v) (h' : NG.OverPl P v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Prove the second alternative. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem qpOf_half : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  classical
  intro D Pq hPq S hS
  have pair := GlobalTheory.T.comap_realSubfield_eq_iff_eq_or_isConjPlace D
  have memq : ∀ P, P ∈ qpOf D Pq S ↔ P ∈ S ∧ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := by
    intro P
    unfold qpOf
    rw [Finset.mem_filter]
  refine ⟨fun P hP => ?_, fun P hP P' hP' hc => ?_⟩
  · by_cases hq : P ∈ qpOf D Pq S
    · exact ⟨P, hq, Or.inl rfl⟩
    · have hn : ¬ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := fun h => hq ((memq P).2 ⟨hP, h⟩)
      push_neg at hn
      obtain ⟨v, hv, -, hin⟩ := hn
      refine ⟨Pq v, (memq _).2 ⟨hin, fun v' hv' => Or.inl ?_⟩, ?_⟩
      · rw [overPl_unique D (hPq v) hv']
      · rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
  · have hPS := ((memq P).1 hP).1
    have hP'S := ((memq P').1 hP').1
    let v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) P
    have hv : NG.OverPl P v := rfl
    have hv' : NG.OverPl P' v := ((pair P P').2 (Or.inr hc)).symm.trans hv
    have hqS : Pq v ∈ S := by
      rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
      · rw [← h]; exact hPS
      · rw [← isConjPl_unique D hc h]; exact hP'S
    have e1 := qpOf_eq D Pq S hP hv hqS
    have e2 := qpOf_eq D Pq S hP' hv' hqS
    have e : P' = P := e2.trans e1.symm
    rw [e] at hc
    exact not_isConjPl_self D (hS P hPS) hc

end GlobalTheory.ChosenHalf
