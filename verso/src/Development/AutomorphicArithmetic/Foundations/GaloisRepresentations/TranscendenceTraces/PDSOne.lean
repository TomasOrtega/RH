import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hL R _ Z S p _ T hT U u b hb`. Take `⟨-, hmono, -, -, -, -, -⟩` from `GlobalTheory.T.etaleLocal_property_calculus_rules`. Establish `h1` using `(GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R T).1 hT (pullback p u) b hb`. Establish `h2` using `hL R T.f (pullback.snd p u) b h1`. Apply `hmono _ _ _ h2` to reduce the goal to its premises.

Introduce `U' g hg`. Take `⟨a, ha⟩` from `hg (pullback p (g ≫ u)) (pbm p g u (g ≫ u) rfl) (pullback.snd p (g ≫ u)) (pbm_snd p g u (g ≫ u) rfl)`. Use `⟨inc p T.X₁ (g ≫ u) a, ?_⟩` and prove the remaining obligations. Rewrite using `[DS.map_inc, ha, DS.res_inc p T.X₂ g u (g ≫ u) rfl]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.dSOne_of :
    LocFinSec → DSOne := by
  intro hL R _ Z S p _ T hT U u b hb
  obtain ⟨-, hmono, -, -, -, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have h1 := (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R T).1 hT (pullback p u) b hb
  have h2 := hL R T.f (pullback.snd p u) b h1
  apply hmono _ _ _ h2
  intro U' g hg
  obtain ⟨a, ha⟩ := hg (pullback p (g ≫ u)) (pbm p g u (g ≫ u) rfl) (pullback.snd p (g ≫ u))
    (pbm_snd p g u (g ≫ u) rfl)
  refine ⟨inc p T.X₁ (g ≫ u) a, ?_⟩
  rw [DS.map_inc, ha, DS.res_inc p T.X₂ g u (g ≫ u) rfl]
