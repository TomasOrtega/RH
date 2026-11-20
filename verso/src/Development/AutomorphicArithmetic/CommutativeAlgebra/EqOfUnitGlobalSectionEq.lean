import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.PicUnit

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.GmInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def coord {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

/- English proof (translation)
The claim follows from `Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)`.
-/
private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.GmInj

/- English proof (translation)
Unfold `UpperTheory.GmInj.coord UpperTheory.GmInj.toLine`. Rewrite using `[Scheme.Hom.comp_appTop]`. Simplify using `[UpperTheory.GmInj.evalT]`.
-/
private theorem gmInj_coord_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.GmInj.coord (UpperTheory.GmInj.toLine a) = a := by
  unfold UpperTheory.GmInj.coord UpperTheory.GmInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.GmInj.evalT]

/- English proof (translation)
Unfold `UpperTheory.GmInj.toLine`. Rewrite using `[← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use `ext1`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `n`. Simplify using `[UpperTheory.GmInj.evalT]`. Simplify using `[UpperTheory.GmInj.evalT]`.
-/
private theorem comp_gmInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.GmInj.toLine a = UpperTheory.GmInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.GmInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.GmInj.evalT]
  · simp [UpperTheory.GmInj.evalT]

/- English proof (translation)
Introduce `U u v h`. Establish `hS` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op U) (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h`. Establish `key : UpperTheory.GmInj.toLine (u : Γ(U, ⊤)) = UpperTheory.GmInj.toLine (v : Γ(U, ⊤))`. Use `(UpperTheory.GmInj.line_sheaf _ hS).isSeparatedFor (fun W f _ => f ≫ UpperTheory.GmInj.toLine (u : Γ(U, ⊤))) _ _ (fun W f hf => rfl) (fun W f hf => ?_)` and prove the remaining obligations. Use `show f ≫ UpperTheory.GmInj.toLine _ = f ≫ UpperTheory.GmInj.toLine _`.

Rewrite using `[comp_gmInj_toLine, comp_gmInj_toLine]`. Establish `h2` using `congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) => ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf`. Establish `h3 : f.appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom v` using `h2`. Rewrite using `[h3]`. Establish `h4` using `congrArg UpperTheory.GmInj.coord key`.

Rewrite `h4` using `[gmInj_coord_toLine, gmInj_coord_toLine]`. Conclude with `Units.ext h4`.
-/
theorem UpperTheory.eq_of_unitGlobalSection_eq :
    ∀ (U : Scheme.{0}) (u v : (Γ(U, ⊤))ˣ), unitSec u = unitSec v → u = v := by
  intro U u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op U)
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.GmInj.toLine (u : Γ(U, ⊤)) = UpperTheory.GmInj.toLine (v : Γ(U, ⊤)) := by
    refine (UpperTheory.GmInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.GmInj.toLine (u : Γ(U, ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.GmInj.toLine _ = f ≫ UpperTheory.GmInj.toLine _
    rw [comp_gmInj_toLine, comp_gmInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.GmInj.coord key
  rw [gmInj_coord_toLine, gmInj_coord_toLine] at h4
  exact Units.ext h4
