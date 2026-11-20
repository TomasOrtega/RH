import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def BoxRosatiSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D' D : DegPre R) (n : ℕ) (pD : IsPowDeg D' D n)
    (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g →
    (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) →
    RosatiAdj D.P.A D.P.L f g → RosatiAdj D'.P.A D'.P.L f' g'

def BoxTauBalSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D' D : DegPre R) (n : ℕ) (pD : IsPowDeg D' D n)
    (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A) (a a' : D.X → D.X), IsMonHom f → IsMonHom g →
    (∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) → (∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) →
    RosatiAdj D.P.A D.P.L f g → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (a' y) = D.c y ≫ g) →
    D.TauBal f g a a' →
    D'.TauBal f' g' (fun y => pD.xe.symm fun i => a (pD.xe y i))
      (fun y => pD.xe.symm fun i => a' (pD.xe y i))

section Pow

variable {S : Scheme.{0}} {A' A : Over S} [GrpObj A'] [GrpObj A] {n : ℕ}

def powMap (p : IsPowGrp A' A n) (f : A ⟶ A) : A' ⟶ A' :=
  p.lim.lift (Fan.mk A' fun i => p.pr i ≫ f)

@[reassoc]
/- English proof (translation)
The claim follows from `p.lim.fac _ ⟨i⟩`.
-/
theorem powMap_pr (p : IsPowGrp A' A n) (f : A ⟶ A) (i : Fin n) : powMap p f ≫ p.pr i = p.pr i ≫ f :=
  p.lim.fac _ ⟨i⟩

/- English proof (translation)
The claim follows from `p.lim.hom_ext fun ⟨i⟩ => h i`.
-/
theorem pow_ext (p : IsPowGrp A' A n) {T : Over S} {x y : T ⟶ A'} (h : ∀ i, x ≫ p.pr i = y ≫ p.pr i) :
    x = y :=
  p.lim.hom_ext fun ⟨i⟩ => h i

/- English proof (translation)
The claim follows from `pow_ext p fun i => by have := p.hom i rw [Category.assoc, powMap_pr, ← Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom] mul_hom := pow_ext p fun i => by have := p.hom i rw [Category.assoc, powMap_pr, ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, Categor …`.
-/
theorem powMap_isMonHom (p : IsPowGrp A' A n) (f : A ⟶ A) [IsMonHom f] : IsMonHom (powMap p f) where
  one_hom := pow_ext p fun i => by
    have := p.hom i
    rw [Category.assoc, powMap_pr, ← Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := pow_ext p fun i => by
    have := p.hom i
    rw [Category.assoc, powMap_pr, ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, powMap_pr]

variable [IsCommMonObj A'] [IsCommMonObj A]

/- English proof (translation)
Use `p.hom i` as an intermediate fact. Rewrite using `[padd, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc]`.
-/
theorem padd_pr (p : IsPowGrp A' A n) {T : Over S} (x y : T ⟶ A') (i : Fin n) :
    padd A' x y ≫ p.pr i = padd A (x ≫ p.pr i) (y ≫ p.pr i) := by
  have := p.hom i
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc]

def powRingAct (p : IsPowGrp A' A n) {O : Type} [Ring O] (ρ : RingAct A O) : RingAct A' O where
  act a := powMap p (ρ.act a)
  hom a := by have := ρ.hom a; exact powMap_isMonHom p _
  map_one := pow_ext p fun i => by rw [powMap_pr, ρ.map_one, Category.comp_id, Category.id_comp]
  map_mul a b := pow_ext p fun i => by
    simp only [powMap_pr, ρ.map_mul, Category.assoc, powMap_pr_assoc]
  map_add a b := pow_ext p fun i => by
    rw [powMap_pr, ρ.map_add, padd_pr, powMap_pr, powMap_pr, padd, padd, comp_lift_assoc]

/- English proof (translation)
The claim follows from `powMap_pr p _ i`.
-/
theorem powRingAct_pr (p : IsPowGrp A' A n) {O : Type} [Ring O] (ρ : RingAct A O) (a : O) (i : Fin n) :
    (powRingAct p ρ).act a ≫ p.pr i = p.pr i ≫ ρ.act a :=
  powMap_pr p _ i

end Pow

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ t P n D' pD`. Use `letI := H.starRing`. Use `letI sm : SMul (𝓞 E) D'.toPre.X := ⟨fun a x => pD.xe.symm (a • pD.xe x)⟩`. Establish `hsm : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x` using `fun a x => pD.xe.apply_symm_apply _`. Use `letI M : Module (𝓞 E) D'.toPre.X := Function.Injective.module (𝓞 E) pD.xe.toAddMonoidHom pD.xe.injective hsm`.

Use `⟨M, ?_⟩` and prove the remaining obligations. Set `ρ` to `powRingAct pD.pw P.oD.onB.toRingAct`. Establish `hpr : ∀ (a : 𝓞 E) (i : Fin n), ρ.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a` using `fun a i => powRingAct_pr _ _ a i`. Establish `rosati : ∀ a : 𝓞 E, RosatiAdj D'.toPre.P.A D'.toPre.P.L (ρ.act a) (ρ.act (star a))` using `fun a => hR V D'.toPre P.D.toPre n pD _ _ _ _ (P.oD.onB.hom a) (P.oD.onB.hom (star a)) (hpr a) (hpr (star a)) (P.oD.onB.rosati a)`. Set `oB : D'.toPre.P.OAct (𝓞 E)` to `{ ρ with rosati := rosati }`.

Use `⟨{ onB := oB, c_lin := ?_, tau_bal := ?_ }, fun a x i => by rw [hsm]; rfl, fun a i => hpr a i⟩` and prove the remaining obligations. Introduce `a y`. Apply `pow_ext pD.pw` to reduce the goal to its premises. Introduce `i`. Express the relevant statement in the definitionally equal form `D'.toPre.c (a • y) ≫ pD.pw.pr i = (D'.toPre.c y ≫ ρ.act a) ≫ pD.pw.pr i`.

Rewrite using `[pD.c_pr, hsm, Pi.smul_apply, P.oD.c_lin, Category.assoc, hpr, ← Category.assoc, pD.c_pr]`. Introduce `a`. Conclude with `hT V D'.toPre P.D.toPre n pD _ _ _ _ (fun y => a • y) (fun y => star a • y) (P.oD.onB.hom a) (P.oD.onB.hom (star a)) (hpr a) (hpr (star a)) (P.oD.onB.rosati a) (fun y => P.oD.c_lin a y) (fun y => P.oD.c_lin (star a) y) (P.oD.tau_bal a)`.
-/
theorem powOAct_holds (hR : BoxRosatiSt) (hT : BoxTauBalSt) : PowOActSt := by
  intro E _ _ _ H V _ _ _ t P n D' pD
  letI := H.starRing
  letI sm : SMul (𝓞 E) D'.toPre.X := ⟨fun a x => pD.xe.symm (a • pD.xe x)⟩
  have hsm : ∀ (a : 𝓞 E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x :=
    fun a x => pD.xe.apply_symm_apply _
  letI M : Module (𝓞 E) D'.toPre.X :=
    Function.Injective.module (𝓞 E) pD.xe.toAddMonoidHom pD.xe.injective hsm
  refine ⟨M, ?_⟩
  let ρ := powRingAct pD.pw P.oD.onB.toRingAct
  have hpr : ∀ (a : 𝓞 E) (i : Fin n), ρ.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a :=
    fun a i => powRingAct_pr _ _ a i
  have rosati : ∀ a : 𝓞 E, RosatiAdj D'.toPre.P.A D'.toPre.P.L (ρ.act a) (ρ.act (star a)) := fun a =>
    hR V D'.toPre P.D.toPre n pD _ _ _ _ (P.oD.onB.hom a) (P.oD.onB.hom (star a)) (hpr a) (hpr (star a))
      (P.oD.onB.rosati a)
  let oB : D'.toPre.P.OAct (𝓞 E) := { ρ with rosati := rosati }
  refine ⟨{ onB := oB, c_lin := ?_, tau_bal := ?_ }, fun a x i => by rw [hsm]; rfl, fun a i => hpr a i⟩
  · intro a y
    apply pow_ext pD.pw
    intro i
    change D'.toPre.c (a • y) ≫ pD.pw.pr i = (D'.toPre.c y ≫ ρ.act a) ≫ pD.pw.pr i
    rw [pD.c_pr, hsm, Pi.smul_apply, P.oD.c_lin, Category.assoc, hpr, ← Category.assoc, pD.c_pr]
  · intro a
    exact hT V D'.toPre P.D.toPre n pD _ _ _ _ (fun y => a • y) (fun y => star a • y) (P.oD.onB.hom a)
      (P.oD.onB.hom (star a)) (hpr a) (hpr (star a)) (P.oD.onB.rosati a)
      (fun y => P.oD.c_lin a y) (fun y => P.oD.c_lin (star a) y) (P.oD.tau_bal a)

end Formalism.MainNotions.ModuliIntegralCharts.H1
