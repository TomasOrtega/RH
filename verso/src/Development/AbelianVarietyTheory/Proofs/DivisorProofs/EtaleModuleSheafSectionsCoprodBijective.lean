import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sec_res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (f ≫ g) x = Sec.res f (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sec_res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sec_coprod : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  intro R _ F U ι V j hU
  let e : ∐ V ≅ U := (coproductIsCoproduct V).coconePointUniqueUpToIso hU
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (coproductIsCoproduct V).comp_coconePointUniqueUpToIso_hom hU ⟨i⟩
  have hb := GlobalTheory.T.sec_sigma_res_bijective R F V
  have hiso : Function.Bijective (fun x : Sec F U => Sec.res e.hom x) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun y => Sec.res e.inv y, fun x => ?_, fun y => ?_⟩
    · simp only
      rw [← sec_res_comp', e.inv_hom_id, sec_res_id']
    · simp only
      rw [← sec_res_comp', e.hom_inv_id, sec_res_id']
  have hfun : (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) =
      (fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a) ∘ (fun x : Sec F U => Sec.res e.hom x) := by
    funext x i
    simp only [Function.comp_apply]
    rw [← sec_res_comp', he i]
  rw [hfun]
  exact hb.comp hiso

end GlobalTheory.EtC
