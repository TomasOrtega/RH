import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.TorusAct

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {T G : C}
    [MonObj T] [MonObj G] (i : T ⟶ G) [IsMonHom i] [Mono i] (f : G ⟶ G) [IsMonHom f] (u : T ⟶ T)
    (h : u ≫ i = i ≫ f) : IsMonHom u where
  one_hom := by
    rw [← cancel_mono i, Category.assoc, h, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    rw [← cancel_mono i, Category.assoc, h, IsMonHom.mul_hom_assoc, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, ← h, ← tensorHom_comp_tensorHom_assoc, IsMonHom.mul_hom]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diagMap_eq_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X) :
    GlobalTheory.Diag.diagMap S u = GlobalTheory.SplitTorus.torusMap S u :=
  (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 (GlobalTheory.Diag.diagMap_chi S u)

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Supply the required witnesses or components.
-/
theorem mono_i (τ : TorusExtension G) : letI := τ.addCommGroup; letI := τ.grpB; Mono τ.i := by
  letI := τ.addCommGroup
  letI := τ.grpB
  exact ⟨fun g h e => τ.isKernel.hom_ext e (toUnit_unique _ _)⟩

/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_restrict (τ : TorusExtension G) (f : G ⟶ G) [IsMonHom f] :
    letI := τ.addCommGroup; letI := τ.grpB; ∀ (b : τ.B ⟶ τ.B), IsMonHom b → f ≫ τ.q = τ.q ≫ b →
      ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ f := by
  letI := τ.addCommGroup
  letI := τ.grpB
  intro b hb hq
  haveI := mono_i τ
  haveI := τ.i_hom
  have w : (τ.i ≫ f) ≫ τ.q = toUnit _ ≫ η := by
    rw [Category.assoc, hq, ← Category.assoc, τ.isKernel.w, Category.assoc, IsMonHom.one_hom]
  let u := τ.isKernel.lift (τ.i ≫ f) (toUnit _) w
  have hu : u ≫ τ.i = τ.i ≫ f := τ.isKernel.lift_fst _ _ _
  haveI : IsMonHom u := isMonHom_of_comp_mono τ.i f u hu
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨φ, hφ ▸ hu⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Equip the data with the indicated structure. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Equip the data with the indicated structure.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_module_diagAct : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G)
    (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB;
    (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) →
      ∃ m : Module O τ.X, letI := m;
        ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  intro K _ G _ τ O _ act
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hb
  haveI := mono_i τ
  haveI := τ.i_hom
  have ex : ∀ a, ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ act.act a := fun a => by
    obtain ⟨b, h1, h2⟩ := hb a
    haveI := act.hom a
    exact exists_restrict τ _ b h1 h2
  choose φ hφ using ex
  have inj : ∀ {α β : τ.X →+ τ.X}, GlobalTheory.SplitTorus.torusMap (Sp K) α ≫ τ.i =
      GlobalTheory.SplitTorus.torusMap (Sp K) β ≫ τ.i → α = β := fun h =>
    GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 h)
  have h1 : φ 1 = AddMonoidHom.id τ.X := inj (by
    rw [hφ, act.one, GlobalTheory.SplitTorus.torusMap_id, Category.comp_id, Category.id_comp])
  have hm : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b => inj (by
    rw [hφ, act.mul, GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, hφ,
      ← Category.assoc _ τ.i, hφ, Category.assoc])
  have ha : ∀ a b, φ (a + b) = φ a + φ b := fun a b => inj (by
    rw [hφ, act.add, GlobalTheory.SplitTorus.torusMap_add, MonObj.mul_comp, hφ, hφ, MonObj.comp_mul])
  let ρ : O →+* AddMonoid.End τ.X := RingHom.mk' ⟨⟨φ, h1⟩, hm⟩ ha
  letI m : Module O τ.X := Module.compHom τ.X ρ
  refine ⟨m, fun a => ?_⟩
  have e : DistribSMul.toAddMonoidHom τ.X a = φ a := rfl
  rw [GlobalTheory.Diag.diagAct_act, e, diagMap_eq_torusMap, hφ]

end GlobalTheory.CompanionTheory.TorusAct
