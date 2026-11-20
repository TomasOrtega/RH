import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]`. Simplify using the standard rewrite rules.
-/
theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

/- English proof (translation)
Assume the negation of the conclusion as `hs`. Apply `h` to reduce the goal to its premises. Establish `key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) → x ∈ w.asIdeal → y ∈ w.asIdeal`. Introduce `x y hxy hx`. Assume the negation of the conclusion as `hy`.

Apply `hs` to reduce the goal to its premises. Use `⟨x, hx, fun y' hy' => ?_⟩` and prove the remaining obligations. Establish `: y' = y`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hy'.trans hxy.symm`.

Rewrite using `[this]` and apply the resulting hypothesis. Introduce `x y hxy`. Use `⟨key x y hxy, key y x ?_⟩` and prove the remaining obligations. Rewrite using `[hxy, host_conj_conj]`.
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
Introduce `D k v` and use `isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)`.
-/
theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
