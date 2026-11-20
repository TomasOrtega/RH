import Mathlib
import Formalism.PeriodIntegrals.ExpTri
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

open Matrix Finset

noncomputable section

namespace PI.ET

/- English proof (translation)
Unfold `PI.ExpTri`. Introduce `n X Y Z U hX hY hZ hU hexp`. Take `⟨ξ, hξ⟩` from `hS n X hX`. Take `⟨η, hη⟩` from `hS n Y hY`. Take `⟨ζ, hζ⟩` from `hS n Z hZ`.

Take `⟨hmaj, hsum⟩` from `hH n X Y Z U ξ η ζ hξ hη hζ hU hexp`. Establish `hζ'` using `hζ`. Take `⟨hanti, -⟩` from `hζ'`. Establish `hsq : ∑ i, ζ i ^ 2 ≤ ∑ i, (ξ i + η i) ^ 2` using `hA n ζ (fun i => ξ i + η i) hanti hmaj hsum`. Rewrite using `[hHS n Z ζ hζ, hHS n X ξ hξ, hHS n Y η hη]`.

Conclude with `le_trans (Real.sqrt_le_sqrt hsq) (hE n ξ η)`.
-/
theorem expTri_of (hS : SpecExists) (hHS : HSEq) (hH : Horn) (hA : AbelSq) (hE : EuclTri) :
    PI.ExpTri := by
  unfold PI.ExpTri
  intro n X Y Z U hX hY hZ hU hexp
  obtain ⟨ξ, hξ⟩ := hS n X hX
  obtain ⟨η, hη⟩ := hS n Y hY
  obtain ⟨ζ, hζ⟩ := hS n Z hZ
  obtain ⟨hmaj, hsum⟩ := hH n X Y Z U ξ η ζ hξ hη hζ hU hexp
  have hζ' := hζ
  obtain ⟨hanti, -⟩ := hζ'

  have hsq : ∑ i, ζ i ^ 2 ≤ ∑ i, (ξ i + η i) ^ 2 :=
    hA n ζ (fun i => ξ i + η i) hanti hmaj hsum
  rw [hHS n Z ζ hζ, hHS n X ξ hξ, hHS n Y η hη]
  exact le_trans (Real.sqrt_le_sqrt hsq) (hE n ξ η)

end PI.ET
