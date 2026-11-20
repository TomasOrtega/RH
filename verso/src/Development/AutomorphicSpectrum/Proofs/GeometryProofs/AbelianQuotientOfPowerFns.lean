import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PicardClassTrivialBySeesawStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Use `letI := T.grpB`. Use `T.q_hom` as an intermediate fact. Use `T.q_flat` as an intermediate fact. Use `T.q_surjective` as an intermediate fact. Use `T.q_quasiCompact` as an intermediate fact.

Establish `: EffectiveEpi T.q` using `GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q`. Use `⟨EffectiveEpi.desc T.q f fun {Z} g₁ g₂ e => ?_, EffectiveEpi.fac _ _ _⟩` and prove the remaining obligations. Establish `h : (g₁ * g₂⁻¹) ≫ T.q = toUnit Z ≫ η[T.B]`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]`. Both sides reduce to the same expression.

Establish `h₁ : T.isKernel.lift _ _ h ≫ T.i = g₁ * g₂⁻¹` using `T.isKernel.lift_fst _ _ h`. Establish `h₂ : g₁ = (T.isKernel.lift _ _ h ≫ T.i) * g₂` using `by rw [h₁, inv_mul_cancel_right]`. Rewrite using `[h₂, MonObj.mul_comp, Category.assoc, hf, MonObj.comp_one, _root_.one_mul]`.
-/
theorem exists_desc {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {Y : Over (Sp k)} [GrpObj Y] (f : G ⟶ Y) [IsMonHom f] (hf : T.i ≫ f = 1) :
    ∃ f' : T.B ⟶ Y, T.q ≫ f' = f := by
  letI := T.grpB
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  refine ⟨EffectiveEpi.desc T.q f fun {Z} g₁ g₂ e => ?_, EffectiveEpi.fac _ _ _⟩
  have h : (g₁ * g₂⁻¹) ≫ T.q = toUnit Z ≫ η[T.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  have h₁ : T.isKernel.lift _ _ h ≫ T.i = g₁ * g₂⁻¹ := T.isKernel.lift_fst _ _ h
  have h₂ : g₁ = (T.isKernel.lift _ _ h ≫ T.i) * g₂ := by rw [h₁, inv_mul_cancel_right]
  rw [h₂, MonObj.mul_comp, Category.assoc, hf, MonObj.comp_one, _root_.one_mul]

/- English proof (translation)
Use `letI := T.addCommGroup`. Use `T.free` as an intermediate fact. Use `T.finite` as an intermediate fact. Use `T.i_hom` as an intermediate fact. Take `⟨b, hb⟩` from `GlobalTheory.splitTorus_to_abelian_const k T.X B hB (T.i ≫ f)`.

Establish `e : (η[splitTorus (Sp k) T.X]) ≫ T.i ≫ f = η[B]` using `IsMonHom.one_hom _`. Rewrite `e` using `[hb]`. Establish `e' : b = η[B]`. Rewrite using `[← e, ← Category.assoc, toUnit_unique (η[splitTorus (Sp k) T.X] ≫ toUnit _) (𝟙 _), Category.id_comp]`. Rewrite using `[hb, e']`.

Both sides reduce to the same expression.
-/
theorem i_comp_eq_one {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G)
    {B : Over (Sp k)} [GrpObj B] (hB : IsAbelianScheme B) (f : G ⟶ B) [IsMonHom f] : T.i ≫ f = 1 := by
  letI := T.addCommGroup
  have := T.free
  have := T.finite
  have := T.i_hom
  obtain ⟨b, hb⟩ := GlobalTheory.splitTorus_to_abelian_const k T.X B hB (T.i ≫ f)
  have e : (η[splitTorus (Sp k) T.X]) ≫ T.i ≫ f = η[B] := IsMonHom.one_hom _
  rw [hb] at e
  have e' : b = η[B] := by
    rw [← e, ← Category.assoc, toUnit_unique (η[splitTorus (Sp k) T.X] ≫ toUnit _) (𝟙 _), Category.id_comp]
  rw [hb, e']
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `letI := T.grpB`. Establish `hB` using `T.isAbelian`. Use `T.q_hom` as an intermediate fact. Use `T.q_flat` as an intermediate fact. Use `T.q_surjective` as an intermediate fact.

Use `T.q_quasiCompact` as an intermediate fact. Establish `: EffectiveEpi T.q` using `GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q`. Establish `canc : ∀ {Y : Over (Sp k)} (f f' : T.B ⟶ Y), T.q ≫ f = T.q ≫ f' → f = f'` using `fun f f' h => (cancel_epi T.q).1 h`. Establish `hact : ∀ r, ∃ f' : T.B ⟶ T.B, T.q ≫ f' = a.act r ≫ T.q` using `fun r => by`. Use `a.hom r` as an intermediate fact.

Conclude with `exists_desc T _ (i_comp_eq_one T hB _)`. Use `choose α hα using hact`. Use `⟨{ act := α, hom := fun r => GlobalTheory.abelianSchemeLaws_all.1.rigidity _ T.B T.B hB hB _ ?_, one := canc _ _ (by rw [hα, a.one, Category.id_comp, Category.comp_id]), mul := fun r s => canc _ _ (by` and prove the remaining obligations. Rewrite using `[hα, a.mul, ← Category.assoc T.q, hα, Category.assoc, Category.assoc, hα]),`. Use `add := fun r s => canc _ _ (by rw [hα, a.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) },`.

Use `fun r => (hα r).symm⟩`. Use `a.hom r` as an intermediate fact. Rewrite using `[← IsMonHom.one_hom T.q, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom]`.
-/
theorem exists_act {k : Type} [Field k] [IsAlgClosed k] {G : Over (Sp k)} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) (T : TorusExtension G) :
    letI := T.grpB
    ∃ b : OAct O T.B, ∀ r, a.act r ≫ T.q = T.q ≫ b.act r := by
  letI := T.grpB
  have hB := T.isAbelian
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have : EffectiveEpi T.q := GlobalTheory.CosetQuotient.effectiveEpi_of_left T.q
  have canc : ∀ {Y : Over (Sp k)} (f f' : T.B ⟶ Y), T.q ≫ f = T.q ≫ f' → f = f' := fun f f' h =>
    (cancel_epi T.q).1 h
  have hact : ∀ r, ∃ f' : T.B ⟶ T.B, T.q ≫ f' = a.act r ≫ T.q := fun r => by
    have := a.hom r
    exact exists_desc T _ (i_comp_eq_one T hB _)
  choose α hα using hact
  refine ⟨{ act := α, hom := fun r => GlobalTheory.abelianSchemeLaws_all.1.rigidity _ T.B T.B hB hB _ ?_,
            one := canc _ _ (by rw [hα, a.one, Category.id_comp, Category.comp_id]),
            mul := fun r s => canc _ _ (by
              rw [hα, a.mul, ← Category.assoc T.q, hα, Category.assoc, Category.assoc, hα]),
            add := fun r s => canc _ _ (by rw [hα, a.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) },
    fun r => (hα r).symm⟩
  have := a.hom r
  rw [← IsMonHom.one_hom T.q, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom]

/- English proof (translation)
Use `letI := T.grpB`. Establish `hB` using `T.isAbelian`. Use `haveI := hB.comm`. Use `T.q_hom` as an intermediate fact. Introduce `act hact a`.

Use `act.hom a` as an intermediate fact. Use `act.hom (H.bar a)` as an intermediate fact. Establish `hL` using `tK.PP.isLB`. Use `set l := cls tK.PP.L hL with hl`. Use `set m := cls M hM with hm`.

Establish `hqm : pull T.q.left m = l` using `((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm`. Establish `lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v` using `fun u v => by`. Rewrite using `[← lam_pull, hqm]`. Establish `adjG : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam l (u ≫ tK.act.act a) v = lam l u (v ≫ tK.act.act (H.bar a))`. Introduce `Z u v`.

Establish `h` using `(cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (tK.adj a)`. Establish `h'` using `congrArg (pull (lift u v).left) ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))`. Simplify `h'` using `only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc]`. Set `D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left` to `fun x y => lam m (x ≫ act.act a) y - lam m x (y ≫ act.act (H.bar a))`. Establish `Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y : Z ⟶ T.B), pull h.left (D x y) = D (h ≫ x) (h ≫ y)`.

Introduce `Z Z' h x y`. Simplify using `only [D, map_sub, pull_lam, Category.assoc]`. Establish `Dq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) = 0`. Introduce `Z u v`. Establish `e₁ : (u ≫ T.q) ≫ act.act a = (u ≫ tK.act.act a) ≫ T.q`.

Rewrite using `[Category.assoc, Category.assoc, hact]`. Establish `e₂ : (v ≫ T.q) ≫ act.act (H.bar a) = (v ≫ tK.act.act (H.bar a)) ≫ T.q`. Rewrite using `[Category.assoc, Category.assoc, hact]`. Simplify using `only [D]`. Rewrite using `[e₁, e₂, lamq, lamq, adjG, sub_self]`.

Establish `D1l : ∀ {Z : Over (Sp k)} (y : Z ⟶ T.B), D 1 y = 0`. Introduce `Z y`. Simplify using `only [D]`. Rewrite using `[MonObj.one_comp, lam_one_left, lam_one_left, sub_self]`. Establish `D1r : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), D x 1 = 0`.

Introduce `Z x`. Simplify using `only [D]`. Rewrite using `[MonObj.one_comp, lam_one_right, lam_one_right, sub_self]`. Establish `hGs` using `tK.semi`. Establish `one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1` using `fun {Z} => MonObj.one_comp _`.

Establish `c₁ : D (fst T.B tK.G) (snd T.B tK.G ≫ T.q) = 0`. Use `GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T tK.G hGs.smooth hGs.geomConnected η[tK.G] _ ?_ ?_` and prove the remaining obligations. Establish `e₁ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ fst T.B tK.G = fst tK.G tK.G ≫ T.q` using `lift_fst _ _`. Establish `e₂ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ snd T.B tK.G ≫ T.q = snd tK.G tK.G ≫ T.q`. Rewrite using `[← Category.assoc, lift_snd]`.

Rewrite using `[Dpull, e₁, e₂]`. Conclude with `Dq _ _`. Establish `e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ fst T.B tK.G = 𝟙 T.B` using `lift_fst _ _`. Establish `e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1`. Rewrite using `[← Category.assoc, lift_snd]`.

Conclude with `one_q`. Rewrite using `[Dpull, e₁, e₂]`. Conclude with `D1r _`. Establish `Dr : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v : Z ⟶ tK.G), D x (v ≫ T.q) = 0`. Introduce `Z x v`.

Establish `h` using `congrArg (pull (lift x v).left) c₁`. Establish `e₂ : lift x v ≫ snd T.B tK.G ≫ T.q = v ≫ T.q` using `by rw [← Category.assoc, lift_snd]`. Rewrite `h` using `[Dpull, map_zero, lift_fst, e₂]`. Conclude with `h`. Establish `c₂ : D (snd T.B T.B) (fst T.B T.B) = 0`.

Use `GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T T.B hB.smooth hB.geomConnected η[T.B] _ ?_ ?_` and prove the remaining obligations. Establish `e₁ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ fst T.B T.B = fst tK.G T.B ≫ T.q` using `lift_fst _ _`. Establish `e₂ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ snd T.B T.B = snd tK.G T.B` using `lift_snd _ _`. Rewrite using `[Dpull, e₁, e₂]`. Conclude with `Dr _ _`.

Establish `e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ fst T.B T.B = 𝟙 T.B` using `lift_fst _ _`. Establish `e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ snd T.B T.B = 1` using `lift_snd _ _`. Rewrite using `[Dpull, e₁, e₂]`. Conclude with `D1l _`. Establish `c₃ : D (fst T.B T.B) (snd T.B T.B) = 0`.

Establish `h` using `congrArg (pull (lift (snd T.B T.B) (fst T.B T.B)).left) c₂`. Rewrite `h` using `[Dpull, map_zero, lift_fst, lift_snd]`. Conclude with `h`. Establish `h₁ : (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M).IsLB` using `LB.isLB_linComb hM _ _`. Establish `h₂ : (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M).IsLB` using `LB.isLB_linComb hM _ _`.

Use `(cls_eq_iff h₁ h₂).1 ?_` and prove the remaining obligations. Rewrite using `[cls_cube_two hM, cls_cube_two hM]`. Conclude with `sub_eq_zero.1 c₃`.
-/
theorem adj_quot {k : Type} [Field k] [IsAlgClosed k] {H : Host E} (tK : SAB H (Sp k)) (T : TorusExtension tK.G)
    (M : LB T.B.left) (hM : M.IsLB) (hbun : LBIso tK.PP.L (M.pull T.q.left)) :
    letI := T.grpB
    ∀ (act : OAct (𝓞 E) T.B), (∀ r, tK.act.act r ≫ T.q = T.q ≫ act.act r) → ∀ a,
      LBIso (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M)
        (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M) := by
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have := T.q_hom
  intro act hact a
  have := act.hom a
  have := act.hom (H.bar a)
  have hL := tK.PP.isLB
  set l := cls tK.PP.L hL with hl
  set m := cls M hM with hm
  have hqm : pull T.q.left m = l := ((cls_eq_iff hL (pull_isLB hM _)).2 hbun).symm
  have lamq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), lam m (u ≫ T.q) (v ≫ T.q) = lam l u v := fun u v => by
    rw [← lam_pull, hqm]
  have adjG : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G),
      lam l (u ≫ tK.act.act a) v = lam l u (v ≫ tK.act.act (H.bar a)) := by
    intro Z u v
    have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (tK.adj a)
    have h' := congrArg (pull (lift u v).left)
      ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
  let D : ∀ {Z : Over (Sp k)}, (Z ⟶ T.B) → (Z ⟶ T.B) → Pic Z.left := fun x y =>
    lam m (x ≫ act.act a) y - lam m x (y ≫ act.act (H.bar a))
  have Dpull : ∀ {Z Z' : Over (Sp k)} (h : Z' ⟶ Z) (x y : Z ⟶ T.B), pull h.left (D x y) = D (h ≫ x) (h ≫ y) := by
    intro Z Z' h x y
    simp only [D, map_sub, pull_lam, Category.assoc]
  have Dq : ∀ {Z : Over (Sp k)} (u v : Z ⟶ tK.G), D (u ≫ T.q) (v ≫ T.q) = 0 := by
    intro Z u v
    have e₁ : (u ≫ T.q) ≫ act.act a = (u ≫ tK.act.act a) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    have e₂ : (v ≫ T.q) ≫ act.act (H.bar a) = (v ≫ tK.act.act (H.bar a)) ≫ T.q := by
      rw [Category.assoc, Category.assoc, hact]
    simp only [D]
    rw [e₁, e₂, lamq, lamq, adjG, sub_self]
  have D1l : ∀ {Z : Over (Sp k)} (y : Z ⟶ T.B), D 1 y = 0 := by
    intro Z y
    simp only [D]
    rw [MonObj.one_comp, lam_one_left, lam_one_left, sub_self]
  have D1r : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B), D x 1 = 0 := by
    intro Z x
    simp only [D]
    rw [MonObj.one_comp, lam_one_right, lam_one_right, sub_self]
  have hGs := tK.semi
  have one_q : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ tK.G) ≫ T.q = 1 := fun {Z} => MonObj.one_comp _
  have c₁ : D (fst T.B tK.G) (snd T.B tK.G ≫ T.q) = 0 := by
    refine GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T tK.G hGs.smooth hGs.geomConnected η[tK.G] _ ?_ ?_
    · have e₁ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ fst T.B tK.G = fst tK.G tK.G ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G tK.G ≫ T.q) (snd tK.G tK.G) ≫ snd T.B tK.G ≫ T.q = snd tK.G tK.G ≫ T.q := by
        rw [← Category.assoc, lift_snd]
      rw [Dpull, e₁, e₂]
      exact Dq _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ fst T.B tK.G = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[tK.G]) ≫ snd T.B tK.G ≫ T.q = 1 := by
        rw [← Category.assoc, lift_snd]
        exact one_q
      rw [Dpull, e₁, e₂]
      exact D1r _
  have Dr : ∀ {Z : Over (Sp k)} (x : Z ⟶ T.B) (v : Z ⟶ tK.G), D x (v ≫ T.q) = 0 := by
    intro Z x v
    have h := congrArg (pull (lift x v).left) c₁
    have e₂ : lift x v ≫ snd T.B tK.G ≫ T.q = v ≫ T.q := by rw [← Category.assoc, lift_snd]
    rw [Dpull, map_zero, lift_fst, e₂] at h
    exact h
  have c₂ : D (snd T.B T.B) (fst T.B T.B) = 0 := by
    refine GlobalTheory.T.picard_class_trivial_by_seesaw k tK.G hGs T T.B hB.smooth hB.geomConnected η[T.B] _ ?_ ?_
    · have e₁ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ fst T.B T.B = fst tK.G T.B ≫ T.q := lift_fst _ _
      have e₂ : lift (fst tK.G T.B ≫ T.q) (snd tK.G T.B) ≫ snd T.B T.B = snd tK.G T.B := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact Dr _ _
    · have e₁ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ fst T.B T.B = 𝟙 T.B := lift_fst _ _
      have e₂ : lift (𝟙 T.B) (toUnit T.B ≫ η[T.B]) ≫ snd T.B T.B = 1 := lift_snd _ _
      rw [Dpull, e₁, e₂]
      exact D1l _
  have c₃ : D (fst T.B T.B) (snd T.B T.B) = 0 := by
    have h := congrArg (pull (lift (snd T.B T.B) (fst T.B T.B)).left) c₂
    rw [Dpull, map_zero, lift_fst, lift_snd] at h
    exact h
  have h₁ : (cubeLB T.B ![fst T.B T.B ≫ act.act a, snd T.B T.B] M).IsLB := LB.isLB_linComb hM _ _
  have h₂ : (cubeLB T.B ![fst T.B T.B, snd T.B T.B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hM, cls_cube_two hM]
  exact sub_eq_zero.1 c₃

/- English proof (translation)
Introduce `E _ _ _ H X t _ k _ _ p _ _ x ⟨T, M, hM, hK, hbun⟩`. Take `⟨PP', cub', sym', adj', prim', m, hm⟩` from `sabPull Out.CubePf.cubePull x t`. Set `tK : SAB H (Sp k)` to `⟨_, IsSemiAbelian.pullback x t.G t.semi, OAct.pullback x t.G t.act, PP', cub', sym', adj', prim'⟩`. Take `⟨w, hw, -, -⟩` from `m.lin`. Establish `hiso : LBIso PP'.L (t.PP.L.pull (pullback.fst t.G.hom x))`.

Rewrite using `[← hm]`. Conclude with `⟨w, hw⟩`. Use `letI := T.grpB`. Establish `hB` using `T.isAbelian`. Use `haveI := hB.comm`.

Establish `hq` using `T.q_hom`. Establish `hP₀` using `pull_isLB t.PP.isLB (pullback.fst t.G.hom x)`. Establish `hqL` using `pull_isLB hM T.q.left`. Establish `hbun' : LBIso tK.PP.L (M.pull T.q.left)` using `LBIso.trans PP'.isLB hP₀ hqL hiso hbun`. Take `⟨act, hact⟩` from `exists_act tK.act T`.

Establish `hadj` using `adj_quot tK T M hM hbun' act hact`. Take `⟨PP, cub, hsym, hPP, hlam, hprim, hadjP⟩` from `GlobalTheory.PrimNorm.exists_primitive_normalisation GlobalTheory.globalFns_holds E H _ T.B act M hB hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme k T.B hB M hM) hadj`. Establish `hP'` using `PP.isLB`. Establish `hL : tK.PP.L.IsLB` using `PP'.isLB`. Establish `hqm : pull T.q.left (cls M hM) = cls tK.PP.L hL` using `((cls_eq_iff hL hqL).2 hbun').symm`.

Establish `hpull : pull T.q.left (cls PP.L hP') = cls tK.PP.L hL`. Establish `h` using `(cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 tK.prim`. Establish `h'` using `(cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP`. Establish `e : cls tK.PP.L hL = lam (cls tK.PP.L hL) (𝟙 _) (tK.act.act H.w0)` using `h.trans (cls_cube_two hL _ _ _)`. Establish `e' : cls PP.L hP' = lam (cls M hM) (𝟙 _) (act.act H.w0)` using `h'.trans (cls_cube_two hM _ _ _)`.

Rewrite using `[e', pull_lam, ← hact, Category.comp_id, ← Category.id_comp T.q, ← Category.assoc, Category.comp_id, ← lam_pull, hqm, ← e]`. Establish `hfin : LBIso tK.PP.L (PP.L.pull T.q.left)`. Rewrite using `[← cls_eq_iff hL (pull_isLB hP' _), cls_pull hP', hpull]`. Establish `hK' : Out.KTriv T.B PP.L` using `GlobalTheory.CM.kTriv_of_lamEq _ T.B M PP.L hM hP' (by simp only [GlobalTheory.CM.LamEq, Category.comp_id]; exact hlam) hK`. Conclude with `⟨{ tB := ⟨T.B, GlobalTheory.isSemiAbelian_of_isAbelianScheme T.B hB, act, PP, cub, hsym, hadjP, hprim⟩ proper := hB.proper ktriv := hK' Ch := T.X acg := T.addCommGroup free := T.free fin := T.finite q := T.q q_hom := hq q_flat := T.q_flat q_surjective := T.q_surjective q_quasiCom …`.
-/
theorem exists_abQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X),
    PowFns t → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X),
    GeomPF t x → Nonempty (AbQuot t x) := by
  intro E _ _ _ H X t _ k _ _ p _ _ x ⟨T, M, hM, hK, hbun⟩
  obtain ⟨PP', cub', sym', adj', prim', m, hm⟩ := sabPull Out.CubePf.cubePull x t
  let tK : SAB H (Sp k) := ⟨_, IsSemiAbelian.pullback x t.G t.semi, OAct.pullback x t.G t.act, PP', cub', sym', adj', prim'⟩
  obtain ⟨w, hw, -, -⟩ := m.lin
  have hiso : LBIso PP'.L (t.PP.L.pull (pullback.fst t.G.hom x)) := by
    rw [← hm]
    exact ⟨w, hw⟩
  letI := T.grpB
  have hB := T.isAbelian
  haveI := hB.comm
  have hq := T.q_hom
  have hP₀ := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have hqL := pull_isLB hM T.q.left
  have hbun' : LBIso tK.PP.L (M.pull T.q.left) := LBIso.trans PP'.isLB hP₀ hqL hiso hbun
  obtain ⟨act, hact⟩ := exists_act tK.act T
  have hadj := adj_quot tK T M hM hbun' act hact
  obtain ⟨PP, cub, hsym, hPP, hlam, hprim, hadjP⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation GlobalTheory.globalFns_holds
    E H _ T.B act M hB hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme k T.B hB M hM) hadj
  have hP' := PP.isLB
  have hL : tK.PP.L.IsLB := PP'.isLB
  have hqm : pull T.q.left (cls M hM) = cls tK.PP.L hL := ((cls_eq_iff hL hqL).2 hbun').symm
  have hpull : pull T.q.left (cls PP.L hP') = cls tK.PP.L hL := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 tK.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : cls tK.PP.L hL = lam (cls tK.PP.L hL) (𝟙 _) (tK.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam (cls M hM) (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, ← hact, Category.comp_id, ← Category.id_comp T.q, ← Category.assoc, Category.comp_id,
      ← lam_pull, hqm, ← e]
  have hfin : LBIso tK.PP.L (PP.L.pull T.q.left) := by
    rw [← cls_eq_iff hL (pull_isLB hP' _), cls_pull hP', hpull]
  have hK' : Out.KTriv T.B PP.L := GlobalTheory.CM.kTriv_of_lamEq _ T.B M PP.L hM hP'
    (by simp only [GlobalTheory.CM.LamEq, Category.comp_id]; exact hlam) hK
  exact ⟨{ tB := ⟨T.B, GlobalTheory.isSemiAbelian_of_isAbelianScheme T.B hB, act, PP, cub, hsym, hadjP, hprim⟩
           proper := hB.proper
           ktriv := hK'
           Ch := T.X
           acg := T.addCommGroup
           free := T.free
           fin := T.finite
           q := T.q
           q_hom := hq
           q_flat := T.q_flat
           q_surjective := T.q_surjective
           q_quasiCompact := T.q_quasiCompact
           i := T.i
           i_hom := T.i_hom
           isKernel := T.isKernel
           act_q := hact
           bun := LBIso.trans hP₀ hL (pull_isLB hP' _) (LBIso.symm hiso) hfin }⟩

end GlobalTheory.CompanionTheory.Ar.AbQ
