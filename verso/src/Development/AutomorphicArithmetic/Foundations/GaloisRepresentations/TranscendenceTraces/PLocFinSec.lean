import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hC hG R _ F G f V U r _ b hb`. Take `⟨W, π, a, hE, hS, ha⟩` from `hC R f V b hb`. Use `haveI := hE`. Use `haveI := hS`. Use `(GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_` and prove the remaining obligations.

Introduce and unpack `U' g ⟨s, hs⟩ V' k r' hk`. Use `⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_res, ha, res_res]`. Use `congr 1`. Rewrite using `[Category.assoc, hs, pullback.lift_fst]`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.locFinSec_of :
    CoverOne → LocFinGeo → LocFinSec := by
  intro hC hG R _ F G f V U r _ b hb
  obtain ⟨W, π, a, hE, hS, ha⟩ := hC R f V b hb
  haveI := hE
  haveI := hS
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_
  rintro U' g ⟨s, hs⟩ V' k r' hk
  refine ⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩
  rw [map_res, ha, res_res]
  congr 1
  rw [Category.assoc, hs, pullback.lift_fst]
