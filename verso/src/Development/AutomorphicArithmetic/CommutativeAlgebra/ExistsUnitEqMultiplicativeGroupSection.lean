import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace UpperTheory
open Polynomial

private def evalX {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A := Polynomial.eval₂RingHom (Int.castRingHom A) a

/- English proof (translation)
Simplify using `[evalX]`.
-/
private lemma evalX_X {A : Type} [CommRing A] (a : A) : evalX a X = a := by simp [evalX]

/- English proof (translation)
Apply `Polynomial.ringHom_ext'` to reduce the goal to its premises. Conclude with `RingHom.ext_int _ _`. Simplify using `[evalX]`.
-/
private lemma evalX_comp {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    f.comp (evalX a) = evalX (f a) := by
  apply Polynomial.ringHom_ext'
  · exact RingHom.ext_int _ _
  · simp [evalX]

private abbrev TT : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private def phi {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ TT :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalX a))

private def psi {V : Scheme.{0}} (f : V ⟶ TT) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

/- English proof (translation)
Unfold `phi`. Rewrite using `[← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use `ext1`. Conclude with `evalX_comp k.appTop.hom a`.
-/
private lemma phi_nat {V W : Scheme.{0}} (k : W ⟶ V) (a : Γ(V, ⊤)) :
    k ≫ phi a = phi (k.appTop.hom a) := by
  unfold phi
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact evalX_comp k.appTop.hom a

/- English proof (translation)
Unfold `psi`. Rewrite using `[Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression.
-/
private lemma psi_nat {V W : Scheme.{0}} (k : W ⟶ V) (f : V ⟶ TT) :
    psi (k ≫ f) = k.appTop.hom (psi f) := by
  unfold psi
  rw [Scheme.Hom.comp_appTop]
  rfl

/- English proof (translation)
Unfold `phi`. Rewrite using `[psi_nat]`. Establish `h` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (evalX a))`. Establish `h2` using `congrArg (fun m => m.hom X) h`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2`.

Unfold `psi`. Rewrite using `[← h2, evalX_X, Scheme.toSpecΓ_appTop]`. Conclude with `ConcreteCategory.congr_hom (Iso.inv_hom_id (Scheme.ΓSpecIso Γ(V, ⊤))) a`.
-/
private lemma psi_phi {V : Scheme.{0}} (a : Γ(V, ⊤)) : psi (phi a) = a := by
  unfold phi
  rw [psi_nat]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (evalX a))
  have h2 := congrArg (fun m => m.hom X) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  unfold psi
  rw [← h2, evalX_X, Scheme.toSpecΓ_appTop]
  exact ConcreteCategory.congr_hom (Iso.inv_hom_id (Scheme.ΓSpecIso Γ(V, ⊤))) a

/- English proof (translation)
The claim follows from `Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)`.
-/
private lemma yo_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj TT) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/- English proof (translation)
Set `x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows` to `fun V g hg => phi (s V g hg)`. Establish `hx : x.Compatible`. Rewrite using `[Presieve.compatible_iff_sieveCompatible]`. Introduce `V W g k hg`. Express the relevant statement in the definitionally equal form `phi (s W (k ≫ g) _) = k ≫ phi (s V g hg)`.

Rewrite using `[phi_nat, hs]`. Take `⟨t, ht, -⟩` from `yo_sheaf S hS x hx`. Use `⟨psi t, fun V g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[← psi_nat]`. Establish `h1 : g ≫ t = phi (s V g hg)` using `ht g hg`.

Rewrite using `[h1, psi_phi]`.
-/
private lemma glueG {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Γ(V, ⊤))
    (hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      k.appTop.hom (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) :
    ∃ a : Γ(U, ⊤), ∀ V g hg, g.appTop.hom a = s V g hg := by
  let x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows := fun V g hg => phi (s V g hg)
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change phi (s W (k ≫ g) _) = k ≫ phi (s V g hg)
    rw [phi_nat, hs]
  obtain ⟨t, ht, -⟩ := yo_sheaf S hS x hx
  refine ⟨psi t, fun V g hg => ?_⟩
  rw [← psi_nat]
  have h1 : g ≫ t = phi (s V g hg) := ht g hg
  rw [h1, psi_phi]

/- English proof (translation)
Set `x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows` to `fun V g _ => phi (g.appTop.hom a)`. Establish `h1 : x.IsAmalgamation (phi a)` using `fun V g hg => phi_nat g a`. Establish `h2 : x.IsAmalgamation (phi b)` using `fun V g hg => by`. Use `(phi_nat g b).trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `phi _ = phi _`.

Rewrite using `[h V g hg]`. Establish `h3 : phi a = phi b` using `(yo_sheaf S hS).isSeparatedFor x _ _ h1 h2`. Rewrite using `[← psi_phi a, h3, psi_phi]`.
-/
private lemma sepG {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (a b : Γ(U, ⊤))
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → g.appTop.hom a = g.appTop.hom b) : a = b := by
  let x : Presieve.FamilyOfElements (yoneda.obj TT) S.arrows := fun V g _ => phi (g.appTop.hom a)
  have h1 : x.IsAmalgamation (phi a) := fun V g hg => phi_nat g a
  have h2 : x.IsAmalgamation (phi b) := fun V g hg => by
    refine (phi_nat g b).trans ?_
    change phi _ = phi _
    rw [h V g hg]
  have h3 : phi a = phi b := (yo_sheaf S hS).isSeparatedFor x _ _ h1 h2
  rw [← psi_phi a, h3, psi_phi]

/- English proof (translation)
Take `⟨a, ha⟩` from `glueG S hS (fun V g hg => (v V g hg : Γ(V, ⊤))) (fun V W g k hg => by`. Use `congrArg Units.val (hv V W g k hg)` as an intermediate fact. Simplify using `using this)`. Take `⟨b, hb⟩` from `glueG S hS (fun V g hg => ((v V g hg)⁻¹ : (Γ(V, ⊤))ˣ)) (fun V W g k hg => by`. Use `congrArg (fun w => ((w⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) (hv V W g k hg)` as an intermediate fact.

Simplify using `using this)`. Establish `hab : a * b = 1` using `sepG S hS _ _ fun V g hg => by`. Rewrite using `[map_mul, ha V g hg, hb V g hg, map_one, Units.mul_inv]`. Use `⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, fun V g hg => Units.ext ?_⟩` and prove the remaining obligations. Simplify using `using ha V g hg`.
-/
private lemma glueU {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (v : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → (Γ(V, ⊤))ˣ)
    (hv : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Units.map k.appTop.hom.toMonoidHom (v V g hg) = v W (k ≫ g) (S.downward_closed hg k)) :
    ∃ u : (Γ(U, ⊤))ˣ, ∀ V g hg, Units.map g.appTop.hom.toMonoidHom u = v V g hg := by
  obtain ⟨a, ha⟩ := glueG S hS (fun V g hg => (v V g hg : Γ(V, ⊤))) (fun V W g k hg => by
    have := congrArg Units.val (hv V W g k hg)
    simpa using this)
  obtain ⟨b, hb⟩ := glueG S hS (fun V g hg => ((v V g hg)⁻¹ : (Γ(V, ⊤))ˣ)) (fun V W g k hg => by
    have := congrArg (fun w => ((w⁻¹ : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) (hv V W g k hg)
    simpa using this)
  have hab : a * b = 1 := sepG S hS _ _ fun V g hg => by
    rw [map_mul, ha V g hg, hb V g hg, map_one, Units.mul_inv]
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, fun V g hg => Units.ext ?_⟩
  simpa using ha V g hg

/- English proof (translation)
The claim follows from `Units.ext (sepG S hS _ _ fun V g hg => by have := congrArg Units.val (h V g hg) simpa using this)`.
-/
private lemma sepU {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u v : (Γ(U, ⊤))ˣ)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
      Units.map g.appTop.hom.toMonoidHom u = Units.map g.appTop.hom.toMonoidHom v) : u = v :=
  Units.ext (sepG S hS _ _ fun V g hg => by
    have := congrArg Units.val (h V g hg)
    simpa using this)

/- English proof (translation)
Establish `h` using `(toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op`. Conclude with `(congrArg (fun m => m.hom (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ))) h).symm`.
-/
private lemma res_unitSec {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  exact (congrArg (fun m => m.hom (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ))) h).symm

/- English proof (translation)
The claim follows from `map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ)) (ULift.up (Additive.ofMul v))`.
-/
private lemma unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) :
    unitSec (u * v) = unitSec u + unitSec v :=
  map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u) : ULift (Additive (Γ(U, ⊤))ˣ)) (ULift.up (Additive.ofMul v))

/- English proof (translation)
Establish `h0 : unitSec (u * v⁻¹) = 0`. Establish `h1` using `unitSec_mul (u * v⁻¹) v`. Rewrite `h1` using `[inv_mul_cancel_right, h]`. Conclude with `(right_eq_add.mp h1)`. Take `⟨S, hS, hl⟩` from `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U (ULift.up (Additive.ofMul (u * v⁻¹)) : ULift (Additive (Γ(U, ⊤))ˣ)) h0`.

Establish `h1 : u * v⁻¹ = 1` using `sepU S hS _ _ fun V g hg => by`. Establish `h2` using `hl V g hg`. Establish `h3 : Additive.ofMul (Units.map g.appTop.hom.toMonoidHom (u * v⁻¹)) = 0` using `congrArg ULift.down h2`. Rewrite using `[map_one]`. Conclude with `h3`.

Conclude with `mul_inv_eq_one.mp h1`.
-/
private lemma unitSec_inj {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) (h : unitSec u = unitSec v) : u = v := by
  have h0 : unitSec (u * v⁻¹) = 0 := by
    have h1 := unitSec_mul (u * v⁻¹) v
    rw [inv_mul_cancel_right, h] at h1
    exact (right_eq_add.mp h1)
  obtain ⟨S, hS, hl⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).2.1 U
    (ULift.up (Additive.ofMul (u * v⁻¹)) : ULift (Additive (Γ(U, ⊤))ˣ)) h0
  have h1 : u * v⁻¹ = 1 := sepU S hS _ _ fun V g hg => by
    have h2 := hl V g hg
    have h3 : Additive.ofMul (Units.map g.appTop.hom.toMonoidHom (u * v⁻¹)) = 0 :=
      congrArg ULift.down h2
    rw [map_one]
    exact h3
  exact mul_inv_eq_one.mp h1

end UpperTheory

open UpperTheory in
/- English proof (translation)
Introduce `X b`. Take `⟨S, hS, h⟩` from `(GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).1 X b`. Establish `h' : ∀ (V : Scheme.{0}) (g : V ⟶ X), S.arrows g → ∃ v : (Γ(V, ⊤))ˣ, unitSec v = Sec.res g b`. Introduce `V g hg`. Take `⟨x, hx⟩` from `h V g hg`.

Conclude with `⟨x.down.toMul, hx⟩`. Use `choose v hv using h'`. Take `⟨u, hu⟩` from `glueU S hS v (fun V W g k hg => by`. Apply `unitSec_inj` to reduce the goal to its premises. Rewrite using `[← res_unitSec, hv, hv]`.

Express the relevant statement in the definitionally equal form `(Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom b) = (Gm.obj.map (k ≫ g).op).hom b`. Rewrite using `[op_comp, Functor.map_comp]`. Use the proof step `rfl)`. Use `⟨u, (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).1 _ _ ⟨S, hS, fun V g hg => ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Sec.res g (unitSec u) = Sec.res g b`.

Rewrite using `[res_unitSec, hu V g hg, hv]`.
-/
theorem UpperTheory.exists_unit_eq_multiplicativeGroup_section :
    ∀ (X : Scheme.{0}) (b : Sec Gm X), ∃ u : (Γ(X, ⊤))ˣ, unitSec u = b := by
  intro X b
  obtain ⟨S, hS, h⟩ := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift ℤ (Scheme.Γ ⋙ unitsF)).1 X b
  have h' : ∀ (V : Scheme.{0}) (g : V ⟶ X), S.arrows g →
      ∃ v : (Γ(V, ⊤))ˣ, unitSec v = Sec.res g b := by
    intro V g hg
    obtain ⟨x, hx⟩ := h V g hg
    exact ⟨x.down.toMul, hx⟩
  choose v hv using h'
  obtain ⟨u, hu⟩ := glueU S hS v (fun V W g k hg => by
    apply unitSec_inj
    rw [← res_unitSec, hv, hv]
    change (Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom b) = (Gm.obj.map (k ≫ g).op).hom b
    rw [op_comp, Functor.map_comp]
    rfl)
  refine ⟨u, (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ Gm X).1 _ _ ⟨S, hS, fun V g hg => ?_⟩⟩
  change Sec.res g (unitSec u) = Sec.res g b
  rw [res_unitSec, hu V g hg, hv]

end
