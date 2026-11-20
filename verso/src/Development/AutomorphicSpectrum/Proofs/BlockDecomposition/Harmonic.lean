import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep

namespace GlobalTheory.CompanionTheory.GKHarmonic

/- English proof (translation)
Introduce `E _ _ a M _ _ _ _ κ L hd q ω hc h0`. Consider the cases of `q with`. Consider the case `zero => exact Or.inl ⟨ω, hc, hd 0 ω hc, h0⟩`. Consider the case `succ q => exact Or.inr ⟨q, ω, hc, hd _ ω hc, fun η hη h => h0 (h.symm.trans (hd q η hη))⟩`.
-/
theorem harmonic : PositivityTheory.Rg.Cz.Harmonic := by
  intro E _ _ a M _ _ _ _ κ L hd q ω hc h0
  cases q with
  | zero => exact Or.inl ⟨ω, hc, hd 0 ω hc, h0⟩
  | succ q => exact Or.inr ⟨q, ω, hc, hd _ ω hc, fun η hη h => h0 (h.symm.trans (hd q η hη))⟩

end GlobalTheory.CompanionTheory.GKHarmonic
