import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalChar

/- English proof (translation)
Introduce `F _ _ _ _ ψ hψ x hx`. Take `⟨hc, h1, h0⟩` from `hψ`. Establish `hb : x ∈ valBall F (addCharConductor ψ)`. Rewrite using `[h0]`. Establish `: x ∈ (valBall F 0 : Set F)`.

Rewrite using `[coe_valBall_zero]`. Conclude with `hx`. Conclude with `this`. Use `isTrivialOn_addCharConductor hc h1 x hb` as an intermediate fact. Simplify using `[this]`.
-/
theorem sPsi : Ad3.LU.SPsi := by
  intro F _ _ _ _ ψ hψ x hx
  obtain ⟨hc, h1, h0⟩ := hψ
  have hb : x ∈ valBall F (addCharConductor ψ) := by
    rw [h0]
    have : x ∈ (valBall F 0 : Set F) := by
      rw [coe_valBall_zero]; exact hx
    exact this
  have := isTrivialOn_addCharConductor hc h1 x hb
  simp [this]

end GlobalTheory.CompanionTheory.LocalChar
