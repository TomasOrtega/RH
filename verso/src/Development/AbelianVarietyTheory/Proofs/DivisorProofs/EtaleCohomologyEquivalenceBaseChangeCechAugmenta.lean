import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem bc_cechAug_eqv : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W),
    Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  intro R _ F S W V r f hE hS U
  obtain ⟨e₁, e₂, he⟩ := bc_cechAug_iso S W V r f U
  have hE' : Etale (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hS' : Surjective (pullback.snd f (pullback.fst r U.hom)) := inferInstance
  have hA : Eqv R (cechAug (pullback.snd f (pullback.fst r U.hom))) F :=
    smooth_surjective_cech_descent_cohomology R (pullback.snd f (pullback.fst r U.hom)) F
  obtain ⟨hiso, hcomp, -, -⟩ := eqv_basic R F
  have h1 : Eqv R e₁.hom F := hiso _ _ _ inferInstance
  have h2 : Eqv R e₂.hom F := hiso _ _ _ inferInstance
  have h3 : Eqv R (e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U) F := by
    rw [he]; exact (hcomp _ _ _ _ _).1 hA h2
  exact (hcomp _ _ _ _ _).2.1 h1 h3

end GlobalTheory.EtC
