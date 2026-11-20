import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.ToricDenomCheck
variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev scaleTh (c : ∀ i, X.abelian₂ i → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := fun i Q lam δ => c i lam * X.th i Q lam δ }

abbrev constTh (c : ∀ i, Finset (HeightOneSpectrum (𝓞 D.host.E)) → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := fun i Q _ _ => c i Q }

/- English proof (translation)
Apply `H.φ₀.injective` to reduce the goal to its premises. Establish `h1` using `H.conjE_apply H.φ₀ (H.conj x)`. Establish `h2` using `H.conjE_apply H.φ₀ x`. Use `h1.trans ?_` and prove the remaining obligations. Use `show starRingEnd ℂ (H.φ₀ (H.conj x)) = _`.

Rewrite using `[h2, Complex.conj_conj]`.
-/
theorem conj_conj' {R : Ranks} (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

/- English proof (translation)
Introduce `x y hy` and use `(h y x (by rw [hy, conj_conj'])).symm`.
-/
theorem isConj_symm {R : Ranks} {H : Host R} {P P' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H P P') : IsConjPl H P' P :=
  fun x y hy => (h y x (by rw [hy, conj_conj'])).symm

end GlobalTheory.ToricDenomCheck
