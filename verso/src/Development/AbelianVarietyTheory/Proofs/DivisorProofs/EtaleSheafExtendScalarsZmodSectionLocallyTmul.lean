import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped ChangeOfRings

namespace GlobalTheory.EtC.ExtOnto

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem unit_surjective {R S : Type 1} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (N : ModuleCat.{1} R) (z : (ModuleCat.extendScalars.{1,1,1} f).obj N) :
    ∃ m : N, ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f).unit.app N).hom m = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • m, ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.unit_app, map_smul, ModuleCat.restrictScalars.smul_def]
    exact (ModuleCat.ExtendScalars.smul_tmul (M := N) f (f r) 1 m).trans
      (congrArg (fun t : S => t ⊗ₜ[R,f] m) (mul_one _))
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem uliftHom_surjective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (uliftHom φ) := by
  intro s
  obtain ⟨r, hr⟩ := hφ s.down
  exact ⟨⟨r⟩, ULift.ext _ _ hr⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem ext_onto : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0})
    (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U),
    Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  intro Q q _ hq M U y
  have hs := uliftHom_surjective (ZMod.castHom hq (ZMod q)) (ZMod.ringHom_surjective _)
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q)
    (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).1 U y
  refine GlobalTheory.EtC.loc_calculus.2.1 _ _ _ h1 ?_
  rintro V g ⟨z, hz⟩
  obtain ⟨m, hm⟩ := unit_surjective _ hs (M.obj.obj (op V)) z
  refine ⟨m, ?_⟩
  subst hm
  exact hz

end GlobalTheory.EtC.ExtOnto
