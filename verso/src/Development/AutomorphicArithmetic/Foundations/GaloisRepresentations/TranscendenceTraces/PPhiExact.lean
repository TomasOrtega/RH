import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `h` using `congrArg (fun φ => ModuleCat.Hom.hom φ x) (((phiPF p R).map f).naturality k.op)`. Simplify using `only [phiPF, phiP, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h`. Conclude with `h.symm`.
-/
private theorem ds_res_map_comm {R : Type} [CommRing R] {Z S : Scheme} (p : Z ⟶ S) {G G' : Shv R}
    (f : G ⟶ G') {W V : Scheme} (k : W ⟶ V) (x : DS p G V) :
    DS.res p G' k (DS.map p f V x) = DS.map p f W (DS.res p G k x) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ x) (((phiPF p R).map f).naturality k.op)
  simp only [phiPF, phiP, ModuleCat.hom_comp, ModuleCat.hom_ofHom] at h
  exact h.symm

/- English proof (translation)
Introduce `hD R _ Z S p _ T hT`. Take `⟨-, hmono, -, -, hloc, -, -⟩` from `GlobalTheory.T.etaleLocal_property_calculus_rules`. Rewrite using `[GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]`. Introduce `U b hb`. Express the relevant statement in the definitionally equal form `Sec ((phi p R).obj T.X₂) U at b`.

Express the relevant statement in the definitionally equal form `Sec.map ((phi p R).map T.g) b = 0 at hb`. Establish `h1` using `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₂)).1 U b`. Apply `hloc` to reduce the goal to its premises. Apply `hmono _ _ _ h1` to reduce the goal to its premises. Introduce and unpack `V g ⟨x0, hx0⟩`.

Take `⟨x, hx⟩ : ∃ x : DS p T.X₂ V, phiSec p T.X₂ V x = Sec.res g b` from `⟨x0, hx0⟩`. Establish `hz : phiSec p T.X₃ V (DS.map p T.g V x) = 0`. Rewrite using `[← phiSec_map, hx, map_res, hb]`. Conclude with `map_zero _`. Establish `h2` using `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₃)).2.1 V _ hz`.

Apply `hloc` to reduce the goal to its premises. Apply `hmono _ _ _ h2` to reduce the goal to its premises. Introduce `W k hk`. Establish `hk' : DS.res p T.X₃ k (DS.map p T.g V x) = 0` using `hk`. Establish `h0 : DS.map p T.g W (DS.res p T.X₂ k x) = 0`.

Rewrite using `[← ds_res_map_comm]`. Conclude with `hk'`. Apply `hmono _ _ _ (hD R p T hT W (DS.res p T.X₂ k x) h0)` to reduce the goal to its premises. Introduce and unpack `W' k' ⟨a, ha⟩`. Use `⟨phiSec p T.X₁ W' a, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Sec.map ((phi p R).map T.f) (phiSec p T.X₁ W' a) = Sec.res ((k' ≫ k) ≫ g) b`. Rewrite using `[phiSec_map, ha, ← phiSec_res, ← phiSec_res, hx]`. Conclude with `(res_res k' k (Sec.res g b)).trans (res_res (k' ≫ k) g b)`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.phiExact_of :
    DSLoc → PhiExact := by
  intro hD R _ Z S p _ T hT
  obtain ⟨-, hmono, -, -, hloc, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  rw [GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  intro U b hb
  change Sec ((phi p R).obj T.X₂) U at b
  change Sec.map ((phi p R).map T.g) b = 0 at hb
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₂)).1 U b
  apply hloc
  apply hmono _ _ _ h1
  rintro V g ⟨x0, hx0⟩
  obtain ⟨x, hx⟩ : ∃ x : DS p T.X₂ V, phiSec p T.X₂ V x = Sec.res g b := ⟨x0, hx0⟩
  have hz : phiSec p T.X₃ V (DS.map p T.g V x) = 0 := by
    rw [← phiSec_map, hx, map_res, hb]
    exact map_zero _
  have h2 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R (phiP p T.X₃)).2.1 V _ hz
  apply hloc
  apply hmono _ _ _ h2
  intro W k hk
  have hk' : DS.res p T.X₃ k (DS.map p T.g V x) = 0 := hk
  have h0 : DS.map p T.g W (DS.res p T.X₂ k x) = 0 := by
    rw [← ds_res_map_comm]
    exact hk'
  apply hmono _ _ _ (hD R p T hT W (DS.res p T.X₂ k x) h0)
  rintro W' k' ⟨a, ha⟩
  refine ⟨phiSec p T.X₁ W' a, ?_⟩
  change Sec.map ((phi p R).map T.f) (phiSec p T.X₁ W' a) = Sec.res ((k' ≫ k) ≫ g) b
  rw [phiSec_map, ha, ← phiSec_res, ← phiSec_res, hx]
  exact (res_res k' k (Sec.res g b)).trans (res_res (k' ≫ k) g b)
