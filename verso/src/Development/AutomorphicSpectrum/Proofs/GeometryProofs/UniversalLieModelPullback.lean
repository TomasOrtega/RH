import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsDiff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LieTransport

/- English proof (translation)
Substitute `hg` using the available equality. Conclude with `h.2 T x y x₀ y₀ hx hy`.
-/
private theorem mul_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact h.2 T x y x₀ y₀ hx hy

/- English proof (translation)
Substitute `hg` using the available equality. Set `o : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)`. Establish `hm : (o * o).left = o.left`. Rewrite using `[mul_left_eq_of_isGrpPullback h T _ rfl 1 1 o o rfl rfl, _root_.mul_one]`. Both sides reduce to the same expression.

Establish `ho : o * o = o` using `Over.OverMorphism.ext hm`. Establish `ho1 : o = 1`. Use `congrArg (· * o⁻¹) ho` as an intermediate fact. Simplify `this` using `[_root_.mul_assoc]`. Rewrite using `[← ho1]`.

Both sides reduce to the same expression.
-/
private theorem one_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ)
    (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have hm : (o * o).left = o.left := by
    rw [mul_left_eq_of_isGrpPullback h T _ rfl 1 1 o o rfl rfl, _root_.mul_one]
    rfl
  have ho : o * o = o := Over.OverMorphism.ext hm
  have ho1 : o = 1 := by
    have := congrArg (· * o⁻¹) ho
    simpa [_root_.mul_assoc] using this
  rw [← ho1]
  rfl

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Use `Spec.map_id (CommRingCat.of R)` and compare the differences between its conclusion and the goal. Use extensionality with `r`. Simplify using the standard rewrite rules.
-/
private theorem specMap_fstHom_comp_algebraMap_eq_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

/- English proof (translation)
Substitute `hx` using the available equality. Establish `hw : ∀ e, ((M.pt e).left ≫ φ) ≫ G.hom = (epsAt (x ≫ f)).hom`. Introduce `e`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w]`. Simplify using `[epsAt]`.

Set `P : W → (epsAt (x ≫ f) ⟶ G)` to `fun e => Over.homMk (U := epsAt (x ≫ f)) (V := G) ((M.pt e).left ≫ φ) (hw e)`. Establish `hP : ∀ e, (P e).left = (M.pt e).left ≫ φ` using `fun e => rfl`. Establish `one_eq` using `one_left_eq_of_isGrpPullback h (Over.mk x) (x ≫ f) rfl`. Establish `hg : Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x ≫ f = (epsAt x).hom ≫ f` using `by simp [epsAt]`. Use `⟨⟨P, ?_, ?_, ?_, ?_, ?_⟩, hP⟩` and prove the remaining obligations.

Introduce `e`. Establish `ht` using `M.tan e`. Unfold `IsTanAt at ht ⊢`. Rewrite using `[hP, ← Category.assoc, ht]`. Conclude with `one_eq.symm`.

Introduce `e e' hee`. Apply `M.inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `h.1.hom_ext` to reduce the goal to its premises. Use `congrArg Over.Hom.left hee` as an intermediate fact.

Simplify `this` using `[P]`. Rewrite using `[Over.w, Over.w]`. Introduce `v hv`. Establish `hvw : v.left ≫ G.hom = (epsAt x).hom ≫ f`. Rewrite using `[Over.w]`.

Simplify using `[epsAt]`. Set `v' : epsAt x ⟶ G'` to `Over.homMk (h.1.lift v.left (epsAt x).hom hvw) (h.1.lift_snd _ _ _)`. Establish `hv' : IsTanAt G' x v'`. Unfold `IsTanAt at hv ⊢`. Apply `h.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc]`. Simplify using `only [v', Over.homMk_left, h.1.lift_fst]`. Rewrite using `[hv, one_eq]`. Rewrite using `[Category.assoc]`. Simplify using `only [v', Over.homMk_left, h.1.lift_snd]`.

Rewrite using `[Over.w]`. Simplify using `only [epsAt, Over.mk_hom]`. Rewrite using `[← Category.assoc, specMap_fstHom_comp_algebraMap_eq_id, Category.id_comp]`. Take `⟨e, he⟩` from `M.onto v' hv'`. Use `⟨e, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations.

Use `show (M.pt e).left ≫ φ = v.left`. Rewrite using `[he]`. Conclude with `h.1.lift_fst _ _ _`. Introduce `e e'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `hm` using `mul_left_eq_of_isGrpPullback h (epsAt x) _ hg (M.pt e) (M.pt e') (P e) (P e') (hP e) (hP e')`. Use `Eq.trans ?_ hm.symm` and prove the remaining obligations. Rewrite using `[hP, M.add]`. Introduce `c e show (M.pt (c • e)).left ≫ φ = _`. Rewrite using `[M.smul, Category.assoc]`.

Both sides reduce to the same expression.
-/
private theorem exists_lieModel_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S') (x' : Spec (CommRingCat.of R) ⟶ S) (hx : x' = x ≫ f)
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) :
    ∃ N : LieModel G x' W, ∀ e, (N.pt e).left = (M.pt e).left ≫ φ := by
  subst hx
  have hw : ∀ e, ((M.pt e).left ≫ φ) ≫ G.hom = (epsAt (x ≫ f)).hom := by
    intro e
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    simp [epsAt]
  let P : W → (epsAt (x ≫ f) ⟶ G) := fun e =>
    Over.homMk (U := epsAt (x ≫ f)) (V := G) ((M.pt e).left ≫ φ) (hw e)
  have hP : ∀ e, (P e).left = (M.pt e).left ≫ φ := fun e => rfl
  have one_eq := one_left_eq_of_isGrpPullback h (Over.mk x) (x ≫ f) rfl
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x ≫ f =
      (epsAt x).hom ≫ f := by simp [epsAt]
  refine ⟨⟨P, ?_, ?_, ?_, ?_, ?_⟩, hP⟩
  · intro e
    have ht := M.tan e
    unfold IsTanAt at ht ⊢
    rw [hP, ← Category.assoc, ht]
    exact one_eq.symm
  · intro e e' hee
    apply M.inj
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · have := congrArg Over.Hom.left hee
      simpa [P] using this
    · rw [Over.w, Over.w]
  · intro v hv
    have hvw : v.left ≫ G.hom = (epsAt x).hom ≫ f := by
      rw [Over.w]; simp [epsAt]
    let v' : epsAt x ⟶ G' := Over.homMk (h.1.lift v.left (epsAt x).hom hvw) (h.1.lift_snd _ _ _)
    have hv' : IsTanAt G' x v' := by
      unfold IsTanAt at hv ⊢
      apply h.1.hom_ext
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_fst]
        rw [hv, one_eq]
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_snd]
        rw [Over.w]
        simp only [epsAt, Over.mk_hom]
        rw [← Category.assoc, specMap_fstHom_comp_algebraMap_eq_id, Category.id_comp]
    obtain ⟨e, he⟩ := M.onto v' hv'
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ φ = v.left
    rw [he]
    exact h.1.lift_fst _ _ _
  · intro e e'
    apply Over.OverMorphism.ext
    have hm := mul_left_eq_of_isGrpPullback h (epsAt x) _ hg (M.pt e) (M.pt e') (P e) (P e') (hP e) (hP e')
    refine Eq.trans ?_ hm.symm
    rw [hP, M.add]
  · intro c e
    show (M.pt (c • e)).left ≫ φ = _
    rw [M.smul, Category.assoc]
    rfl

/- English proof (translation)
Establish `hpt0 : M.pt 0 = 1`. Establish `h0` using `M.add 0 0`. Rewrite `h0` using `[add_zero]`. Use `congrArg (· * (M.pt 0)⁻¹) h0` as an intermediate fact. Simplify `this.symm` using `[_root_.mul_assoc]`.

Establish `tan : ∀ (b : O) (e : W), IsTanAt G x (M.pt e ≫ a.act b)`. Introduce `b e`. Establish `ht` using `M.tan e`. Establish `hh` using `a.hom b`. Unfold `IsTanAt at ht ⊢`.

Rewrite using `[Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]`. Use `choose A hA using fun (b : O) (e : W) => M.onto (M.pt e ≫ a.act b) (tan b e)`. Establish `hadd : ∀ b e e', A b (e + e') = A b e + A b e'`. Introduce `b e e'`. Establish `hh` using `a.hom b`.

Apply `M.inj` to reduce the goal to its premises. Rewrite using `[hA, M.add, M.add, hA, hA, MonObj.mul_comp]`. Establish `hsmul : ∀ b (c : R) e, A b (c • e) = c • A b e`. Introduce `b c e`. Apply `M.inj` to reduce the goal to its premises.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hA, Over.comp_left, M.smul, M.smul, hA, Over.comp_left, Category.assoc]`. Set `L : O → Module.End R W` to `fun b => { toFun := A b, map_add' := hadd b, map_smul' := fun c e => by simpa using hsmul b c e }`. Establish `hL : ∀ b e, L b e = A b e` using `fun _ _ => rfl`. Establish `hone : L 1 = 1`.

Use extensionality with `e`. Apply `M.inj` to reduce the goal to its premises. Rewrite using `[hL, hA, a.one, Category.comp_id]`. Both sides reduce to the same expression. Establish `hmul : ∀ b b', L (b * b') = L b * L b'`.

Introduce `b b'`. Use extensionality with `e`. Apply `M.inj` to reduce the goal to its premises. Rewrite using `[Module.End.mul_apply, hL, hL, hL, hA, hA, hA, mul_comm, a.mul, Category.assoc]`. Establish `haddL : ∀ b b', L (b + b') = L b + L b'`.

Introduce `b b'`. Use extensionality with `e`. Apply `M.inj` to reduce the goal to its premises. Rewrite using `[LinearMap.add_apply, hL, hL, hL, hA, M.add, hA, hA, a.add, MonObj.comp_mul]`. Set `ρ : O →+* Module.End R W` to `RingHom.mk' ⟨⟨L, hone⟩, hmul⟩ haddL`.

Conclude with `⟨ρ, fun b e => hA b e⟩`.
-/
private theorem exists_isActOf_geometry {S : Scheme} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {W : Type} [AddCommGroup W] [Module R W]
    (M : LieModel G x W) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ ρ : O →+* Module.End R W, M.IsActOf a.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h0 := M.add 0 0
    rw [add_zero] at h0
    have := congrArg (· * (M.pt 0)⁻¹) h0
    simpa [_root_.mul_assoc] using this.symm
  have tan : ∀ (b : O) (e : W), IsTanAt G x (M.pt e ≫ a.act b) := by
    intro b e
    have ht := M.tan e
    have hh := a.hom b
    unfold IsTanAt at ht ⊢
    rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]
  choose A hA using fun (b : O) (e : W) => M.onto (M.pt e ≫ a.act b) (tan b e)
  have hadd : ∀ b e e', A b (e + e') = A b e + A b e' := by
    intro b e e'
    have hh := a.hom b
    apply M.inj
    rw [hA, M.add, M.add, hA, hA, MonObj.mul_comp]
  have hsmul : ∀ b (c : R) e, A b (c • e) = c • A b e := by
    intro b c e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hA, Over.comp_left, M.smul, M.smul, hA, Over.comp_left, Category.assoc]
  let L : O → Module.End R W := fun b =>
    { toFun := A b, map_add' := hadd b, map_smul' := fun c e => by simpa using hsmul b c e }
  have hL : ∀ b e, L b e = A b e := fun _ _ => rfl
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, hA, a.one, Category.comp_id]
    rfl
  have hmul : ∀ b b', L (b * b') = L b * L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, hA, hA, hA, mul_comm, a.mul, Category.assoc]
  have haddL : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [LinearMap.add_apply, hL, hL, hL, hA, M.add, hA, hA, a.add, MonObj.comp_mul]
  let ρ : O →+* Module.End R W := RingHom.mk' ⟨⟨L, hone⟩, hmul⟩ haddL
  exact ⟨ρ, fun b e => hA b e⟩

/- English proof (translation)
Introduce `b e`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `h1` using `hM b e`. Rewrite using `[hN, h1, Over.comp_left, Over.comp_left, hN, Category.assoc, hact, Category.assoc]`.
-/
private theorem isActOf_of_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S'} {x' : Spec (CommRingCat.of R) ⟶ S}
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) (N : LieModel G x' W)
    (hN : ∀ e, (N.pt e).left = (M.pt e).left ≫ φ) {O : Type} [CommRing O]
    (act' : O → (G' ⟶ G')) (act : O → (G ⟶ G))
    (hact : ∀ b, (act' b).left ≫ φ = φ ≫ (act b).left)
    (ρ : O →+* Module.End R W) (hM : M.IsActOf act' ρ) : N.IsActOf act ρ := by
  intro b e
  apply Over.OverMorphism.ext
  have h1 := hM b e
  rw [hN, h1, Over.comp_left, Over.comp_left, hN, Category.assoc, hact, Category.assoc]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y F _ y`. Take `⟨W, i1, i2, ⟨M0⟩⟩` from `lieModel_exists _ Y.oF.t.G F y`. Apply the tactic sequence `obtain ⟨ρ, hρ⟩ := exists_isActOf_geometry M0 Y.oF.t.act`. Take `⟨Mu, hMu⟩` from `exists_lieModel_pullback Y.m0.toSABMap.cart y (under y) rfl M0`. Take `⟨Mz, hMz⟩` from `exists_lieModel_pullback Y.m.cart y (y ≫ Y.j) rfl M0`.

Use `⟨W, i1, i2, Mu, Mz, ρ, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isActOf_of_pullback M0 Mu hMu _ _ (fun b => Y.m0.toSABMap.act b) ρ hρ`. Conclude with `isActOf_of_pullback M0 Mz hMz _ _ (fun b => Y.m.act b) ρ hρ`. Introduce `e`. Unfold `SameVec`.

Conclude with `⟨(M0.pt e).left, Over.w (M0.pt e), (hMu e).symm, (hMz e).symm⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  intro E _ _ _ H D l Xo c O _ β Y F _ y
  obtain ⟨W, i1, i2, ⟨M0⟩⟩ := lieModel_exists _ Y.oF.t.G F y
  obtain ⟨ρ, hρ⟩ := exists_isActOf_geometry M0 Y.oF.t.act
  obtain ⟨Mu, hMu⟩ := exists_lieModel_pullback Y.m0.toSABMap.cart y (under y) rfl M0
  obtain ⟨Mz, hMz⟩ := exists_lieModel_pullback Y.m.cart y (y ≫ Y.j) rfl M0
  refine ⟨W, i1, i2, Mu, Mz, ρ, ?_, ?_, ?_⟩
  · exact isActOf_of_pullback M0 Mu hMu _ _ (fun b => Y.m0.toSABMap.act b) ρ hρ
  · exact isActOf_of_pullback M0 Mz hMz _ _ (fun b => Y.m.act b) ρ hρ
  · intro e
    unfold SameVec
    exact ⟨(M0.pt e).left, Over.w (M0.pt e), (hMu e).symm, (hMz e).symm⟩

end GlobalTheory.CompanionTheory.Ar.LieTransport
