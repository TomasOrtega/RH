import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
