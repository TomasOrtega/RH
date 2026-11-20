import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.UnitsInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def ofLine {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

/- English proof (translation)
The claim follows from `Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)`.
-/
private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.UnitsInj

/- English proof (translation)
Unfold `UpperTheory.UnitsInj.ofLine UpperTheory.UnitsInj.toLine`. Rewrite using `[Scheme.Hom.comp_appTop]`. Simplify using `[UpperTheory.UnitsInj.evalT]`.
-/
private theorem unitsInj_ofLine_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.UnitsInj.ofLine (UpperTheory.UnitsInj.toLine a) = a := by
  unfold UpperTheory.UnitsInj.ofLine UpperTheory.UnitsInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.UnitsInj.evalT]

/- English proof (translation)
Unfold `UpperTheory.UnitsInj.toLine`. Rewrite using `[← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use `ext1`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `n`. Simplify using `[UpperTheory.UnitsInj.evalT]`. Simplify using `[UpperTheory.UnitsInj.evalT]`.
-/
private theorem comp_unitsInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.UnitsInj.toLine a = UpperTheory.UnitsInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.UnitsInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.UnitsInj.evalT]
  · simp [UpperTheory.UnitsInj.evalT]

/- English proof (translation)
Introduce `R _`. Use `⟨?_, fun b => UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b⟩` and prove the remaining obligations. Introduce `u v h`. Establish `hS` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op (Spec (CommRingCat.of R))) (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h`. Establish `key : UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)) = UpperTheory.UnitsInj.toLine (v : Γ(Spec (CommRingCat.of R), ⊤))`.

Use `(UpperTheory.UnitsInj.line_sheaf _ hS).isSeparatedFor (fun W f _ => f ≫ UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤))) _ _ (fun W f hf => rfl) (fun W f hf => ?_)` and prove the remaining obligations. Use `show f ≫ UpperTheory.UnitsInj.toLine _ = f ≫ UpperTheory.UnitsInj.toLine _`. Rewrite using `[comp_unitsInj_toLine, comp_unitsInj_toLine]`. Establish `h2` using `congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) => ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf`. Establish `h3 : f.appTop.hom (u : Γ(Spec (CommRingCat.of R), ⊤)) = f.appTop.hom v` using `h2`.

Rewrite using `[h3]`. Establish `h4` using `congrArg UpperTheory.UnitsInj.ofLine key`. Rewrite `h4` using `[unitsInj_ofLine_toLine, unitsInj_ofLine_toLine]`. Conclude with `Units.ext h4`.
-/
theorem UpperTheory.unitSections_multiplicativeGroup_bijective_affine :
    ∀ (R : Type) [CommRing R], Function.Bijective
        (unitSec : (Γ(Spec (CommRingCat.of R), ⊤))ˣ → Sec Gm (Spec (CommRingCat.of R))) := by
  intro R _
  refine ⟨?_, fun b => UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b⟩
  intro u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op (Spec (CommRingCat.of R)))
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)) =
      UpperTheory.UnitsInj.toLine (v : Γ(Spec (CommRingCat.of R), ⊤)) := by
    refine (UpperTheory.UnitsInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.UnitsInj.toLine _ = f ≫ UpperTheory.UnitsInj.toLine _
    rw [comp_unitsInj_toLine, comp_unitsInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(Spec (CommRingCat.of R), ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.UnitsInj.ofLine key
  rw [unitsInj_ofLine_toLine, unitsInj_ofLine_toLine] at h4
  exact Units.ext h4
