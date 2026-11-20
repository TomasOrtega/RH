import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

/- English proof (translation)
Establish `h : Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL))`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (NumberField.RingOfIntegers D.what₂.LL)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField _)⟩⟩`. Conclude with `h.map D.plEq.symm`.
-/
theorem nonempty_places_of_record (D : D7) : Nonempty D.what₂.places.Pl := by
  have h : Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.what₂.LL)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
      (NumberField.RingOfIntegers.not_isField _)⟩⟩
  exact h.map D.plEq.symm

/- English proof (translation)
Introduce `eps Fm`. Use `⟨0, fun x _ hx i j hj z => ?_⟩` and prove the remaining obligations. Take `⟨w⟩` from `nonempty_places_of_record (Fm.D x i)`. Use `(Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_` and prove the remaining obligations. Simplify using `only [SizeData₂.lifts, Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[tauPl]`.
-/
theorem fill_eq_wPl : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)),
      fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  refine ⟨0, fun x _ hx i j hj z => ?_⟩
  obtain ⟨w⟩ := nonempty_places_of_record (Fm.D x i)
  refine (Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_
  · simp only [SizeData₂.lifts, Finset.mem_Icc]; omega
  · simp [tauPl]

end GlobalTheory
