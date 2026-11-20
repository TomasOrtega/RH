import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGLStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

/- English proof (translation)
Introduce `hBZ hSeg hRing k _ _ _ _`. Take `⟨Z, hZ⟩` from `GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing hSeg k`. Take `⟨Ψ, h1, hmul, hX⟩` from `hRing k Z hZ`. Use `⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂`.

Conclude with `⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩`.
-/
theorem zelevinskyPolynomialRing_of_parts :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  intro hBZ hSeg hRing k _ _ _ _
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing hSeg k
  obtain ⟨Ψ, h1, hmul, hX⟩ := hRing k Z hZ
  refine ⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩
  have h := GlobalTheory.T.parabolicProduct_hasFiniteLength_GL hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩

end GlobalTheory
