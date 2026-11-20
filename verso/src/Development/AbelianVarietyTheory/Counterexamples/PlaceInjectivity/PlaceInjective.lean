import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory

namespace GlobalTheory.VolRatioCheck

/- English proof (translation)
The claim follows from `((factEmb D.R D.host).2 _).2 (D.eTau ρ).2`.
-/
theorem embOf_mem (D : D7) (ρ : D.what₂.Tau) :
    embOf D ρ ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau ρ).2

/- English proof (translation)
Introduce `ρ ρ' h`. Establish `hb` using `(factEmb D.R D.host).1`. Break down `InfinitePlace.mk_eq_iff.1 h with h1 | h1` into its components or cases. Conclude with `D.eTau.injective (Subtype.ext (hb.1 h1))`. It suffices to derive a contradiction.

Establish `e1` using `embOf_mem D ρ`. Establish `e2` using `embOf_mem D ρ'`. Rewrite `e2` using `[← h1]`. Conclude with `(D.host.der.cmType.1 _).1 e1 e2`.
-/
theorem place_injective (D : D7) :
    Function.Injective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  intro ρ ρ' h
  have hb := (factEmb D.R D.host).1
  rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
  · exact D.eTau.injective (Subtype.ext (hb.1 h1))
  · exfalso
    have e1 := embOf_mem D ρ
    have e2 := embOf_mem D ρ'
    rw [← h1] at e2
    exact (D.host.der.cmType.1 _).1 e1 e2

/- English proof (translation)
Establish `h1 : Nat.card D.what₂.Tau = D.R.f`. Rewrite using `[Nat.card_congr D.eTau]`. Conclude with `(factCardPsi D.R D.host).1`. Establish `h2 : Nat.card (InfinitePlace D.host.E) = D.R.f`. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `fDeg_host D`. Conclude with `(place_injective D).bijective_of_nat_card_le (by omega)`.
-/
theorem place_bijective (D : D7) :
    Function.Bijective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  have h1 : Nat.card D.what₂.Tau = D.R.f := by
    rw [Nat.card_congr D.eTau]; exact (factCardPsi D.R D.host).1
  have h2 : Nat.card (InfinitePlace D.host.E) = D.R.f := by
    rw [Nat.card_eq_fintype_card]; exact fDeg_host D
  exact (place_injective D).bijective_of_nat_card_le (by omega)

end GlobalTheory.VolRatioCheck

end
