import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hC hN Z S p _ U hU hD hI`. Take `⟨B, _, _, v, hfin, hpb⟩` from `hC p Γ(S, U) hU.fromSpec`. Take `⟨w, hw⟩` from `hN Γ(S, U) B`. Conclude with `⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.normAff_of :
    Chart → NormSpec → NormAff := by
  intro hC hN Z S p _ U hU hD hI
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC p Γ(S, U) hU.fromSpec
  obtain ⟨w, hw⟩ := hN Γ(S, U) B
  exact ⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩
