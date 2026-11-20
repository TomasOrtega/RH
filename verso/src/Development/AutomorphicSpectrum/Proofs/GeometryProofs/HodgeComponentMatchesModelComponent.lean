import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlag
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericPointFieldIso
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 hgen`. Take `⟨ψ, hψ⟩` from `GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq Y.X _ _ 𝔐.ξ₀ (Z.ξ₀ ≫ Y.j) 𝔐.gen₀ Z.gen hgen`. Establish `hdom' : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom (𝔐.fn.comp ψ.toRingHom)) ≫ (Z.ξ₀ ≫ Y.j)`. Establish `h1 : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀` using `𝔐.fn_over`. Establish `h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Z.ξ₀ ≫ Y.j) = 𝔐.ξ₀` using `hψ`.

Rewrite using `[h1, ← h2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`. Establish `hdom : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f (𝔐.fn.comp ψ.toRingHom)` using `hdom'`. Establish `key : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))`. Establish `e1` using `𝔐.cst_over`. Establish `e2` using `Z.over_inc`.

Establish `e3` using `Y.jQ_over`. Rewrite using `[← e1, ← Category.assoc, hdom', ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]`. Simplify using `only [Category.assoc]`. Rewrite using `[pullback.condition, ← Category.assoc Y.jQ, e3, ← Category.assoc Z.ξ₀, e2]`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]`.

Establish `hcst : (𝔐.fn.comp ψ.toRingHom).comp Z.inc = 𝔐.cst`. Establish `k0 : Spec.map (CommRingCat.ofHom (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F))) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)))` using `key`. Establish `k1` using `congrArg CommRingCat.Hom.hom (Spec.map_injective k0)`. Simplify using `only [CommRingCat.hom_ofHom] at k1`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) k1`.

Use `letI := CategoryTheory.Over.cartesianMonoidalCategory 𝔐.X`. Use `letI := CategoryTheory.Over.cartesianMonoidalCategory Y.X`. Use `letI : CategoryTheory.GrpObj 𝔐.t.G := 𝔐.t.grp`. Use `letI : CategoryTheory.GrpObj Y.t.G := Y.t.grp`. Use `letI : Group (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := CategoryTheory.Hom.group`.

Use `letI : Group (Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group`. Use `letI : Group (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group`. Use `letI : Group (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group`. Establish `hpb : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback 𝔐.t.G Y.t.G 𝔐.f 𝔐.m.φ` using `𝔐.m.cart`. Establish `hone : (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ = (1 : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G).left`.

Take `⟨o, ho⟩ : ∃ o : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, o.left = (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ` from `⟨Over.homMk ((1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ) (by`. Rewrite using `[Category.assoc, hpb.1.w, ← Category.assoc, Over.w]`. Use the proof step `rfl), rfl⟩`. Establish `hoo : o * o = o`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hpb.2 (Over.mk 𝔐.ξ) 1 1 o o ho ho, mul_one, ho]`. Establish `ho1 : o = 1` using `by simpa using hoo`. Rewrite using `[← ho, ho1]`. Establish `hT : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) = Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)`. Simplify using `[GlobalTheory.CompanionTheory.Ar.epsAt]`.

Establish `hx0 : ∀ e : 𝔐.Li, ((𝔐.M.pt e).left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)).hom`. Introduce `e`. Rewrite using `[Category.assoc, hpb.1.w, ← Category.assoc, Over.w]`. Both sides reduce to the same expression. Set `x₀ : 𝔐.Li → (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G)` to `fun e => Over.homMk ((𝔐.M.pt e).left ≫ 𝔐.m.φ) (hx0 e)`.

Set `pt' : 𝔐.Li → (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G)` to `fun e => eqToHom hT ≫ x₀ e`. Establish `hleft : ∀ e, (pt' e).left = (𝔐.M.pt e).left ≫ 𝔐.m.φ`. Introduce `e`. Simplify using `[pt', x₀]`. Establish `hx0mul : ∀ e e', x₀ (e + e') = x₀ e * x₀ e'`.

Introduce `e e'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hpb.2 (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) (𝔐.M.pt e) (𝔐.M.pt e') (x₀ e) (x₀ e') rfl rfl, ← 𝔐.M.add]`. Both sides reduce to the same expression. Establish `hadd : ∀ e e', pt' (e + e') = pt' e * pt' e'`.

Introduce `e e'`. Simplify using `only [pt']`. Rewrite using `[hx0mul, MonObj.comp_mul]`. Establish `htan : ∀ e, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) (pt' e)`. Introduce `e`.

Establish `h` using `𝔐.M.tan e`. Unfold `GlobalTheory.CompanionTheory.Ar.IsTanAt at h ⊢`. Rewrite using `[hleft, ← Category.assoc, h, hone]`. Establish `hinj : Function.Injective pt'`. Introduce `e e' hee`.

Apply `𝔐.M.inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hpb.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← hleft, ← hleft, hee]`. Rewrite using `[Over.w, Over.w]`.

Establish `hfa : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp (algebraMap Ω (DualNumber Ω)) = RingHom.id Ω`. Use extensionality with `r`. Simplify using the standard rewrite rules. Establish `honto : ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) v → ∃ e, pt' e = v`. Introduce `v hv`.

Establish `hw : v.left ≫ Y.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f`. Rewrite using `[Over.w]`. Simplify using `[GlobalTheory.CompanionTheory.Ar.epsAt]`. Take `⟨L, hL1, hL2⟩ : ∃ L, L ≫ 𝔐.m.φ = v.left ∧ L ≫ 𝔐.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom` from `⟨_, hpb.1.lift_fst _ _ hw, hpb.1.lift_snd _ _ hw⟩`. Establish `htw : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G 𝔐.ξ (Over.homMk (U` using `GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) L hL2) := by`.

Unfold `GlobalTheory.CompanionTheory.Ar.IsTanAt at hv ⊢`. Apply `hpb.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.m.φ = _`. Rewrite using `[hL1, hv, hone]`.

Rewrite using `[Category.assoc]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.t.G.hom = _`. Rewrite using `[hL2, Over.w]`. Use `show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ 𝔐.ξ = 𝔐.ξ`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`.

Take `⟨e, he⟩` from `𝔐.M.onto _ htw`. Use `⟨e, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hleft, he]`. Conclude with `hL1`. Establish `hsmul : ∀ (a : Ω) (e : 𝔐.Li), (pt' (a • e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul a)) ≫ (pt' e).left`.

Introduce `a e`. Rewrite using `[hleft, hleft, 𝔐.M.smul, Category.assoc]`. Set `M' : GlobalTheory.CompanionTheory.Ar.LieModel Y.t.G (𝔐.ξ ≫ 𝔐.f) 𝔐.Li` to `⟨pt', htan, hinj, honto, hadd, hsmul⟩`. Establish `hsm : AlgebraicGeometry.Smooth Y.t.G.hom` using `@ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ Y.t.semi`. Take `⟨j, hj1, hj2, -⟩` from `GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.exists_ext hsm (𝔐.fn.comp ψ.toRingHom) (Z.ξ₀ ≫ Y.j) (𝔐.ξ ≫ 𝔐.f) hdom'.symm Z.M M'`.

Use `⟨𝔐.fn.comp ψ.toRingHom, j, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.CompanionTheory.Ar.Flat.CptIn.IsTie`. Conclude with `⟨hdom, hcst, hj2, fun e => (hleft (j e)).symm.trans (hj1 e)⟩`.
-/
theorem exists_isTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 hgen
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq Y.X _ _ 𝔐.ξ₀ (Z.ξ₀ ≫ Y.j) 𝔐.gen₀ Z.gen hgen
  have hdom' : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom (𝔐.fn.comp ψ.toRingHom)) ≫ (Z.ξ₀ ≫ Y.j) := by
    have h1 : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀ := 𝔐.fn_over
    have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Z.ξ₀ ≫ Y.j) = 𝔐.ξ₀ := hψ
    rw [h1, ← h2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f (𝔐.fn.comp ψ.toRingHom) := hdom'
  have key : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    have e1 := 𝔐.cst_over
    have e2 := Z.over_inc
    have e3 := Y.jQ_over
    rw [← e1, ← Category.assoc, hdom', ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, e3, ← Category.assoc Z.ξ₀, e2]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hcst : (𝔐.fn.comp ψ.toRingHom).comp Z.inc = 𝔐.cst := by
    have k0 : Spec.map (CommRingCat.ofHom (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F))) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) := key
    have k1 := congrArg CommRingCat.Hom.hom (Spec.map_injective k0)
    simp only [CommRingCat.hom_ofHom] at k1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) k1
  letI := CategoryTheory.Over.cartesianMonoidalCategory 𝔐.X
  letI := CategoryTheory.Over.cartesianMonoidalCategory Y.X
  letI : CategoryTheory.GrpObj 𝔐.t.G := 𝔐.t.grp
  letI : CategoryTheory.GrpObj Y.t.G := Y.t.grp
  letI : Group (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  have hpb : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback 𝔐.t.G Y.t.G 𝔐.f 𝔐.m.φ := 𝔐.m.cart
  have hone : (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ = (1 : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G).left := by
    obtain ⟨o, ho⟩ : ∃ o : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, o.left = (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ :=
      ⟨Over.homMk ((1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ) (by
        rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl), rfl⟩
    have hoo : o * o = o := by
      apply Over.OverMorphism.ext
      rw [hpb.2 (Over.mk 𝔐.ξ) 1 1 o o ho ho, mul_one, ho]
    have ho1 : o = 1 := by simpa using hoo
    rw [← ho, ho1]
  have hT : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) = Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) := by
    simp [GlobalTheory.CompanionTheory.Ar.epsAt]
  have hx0 : ∀ e : 𝔐.Li, ((𝔐.M.pt e).left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)).hom := by
    intro e
    rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : 𝔐.Li → (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := fun e => Over.homMk ((𝔐.M.pt e).left ≫ 𝔐.m.φ) (hx0 e)
  let pt' : 𝔐.Li → (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := fun e => eqToHom hT ≫ x₀ e
  have hleft : ∀ e, (pt' e).left = (𝔐.M.pt e).left ≫ 𝔐.m.φ := by
    intro e
    simp [pt', x₀]
  have hx0mul : ∀ e e', x₀ (e + e') = x₀ e * x₀ e' := by
    intro e e'
    apply Over.OverMorphism.ext
    rw [hpb.2 (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) (𝔐.M.pt e) (𝔐.M.pt e') (x₀ e) (x₀ e') rfl rfl, ← 𝔐.M.add]
    rfl
  have hadd : ∀ e e', pt' (e + e') = pt' e * pt' e' := by
    intro e e'
    simp only [pt']
    rw [hx0mul, MonObj.comp_mul]
  have htan : ∀ e, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) (pt' e) := by
    intro e
    have h := 𝔐.M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h ⊢
    rw [hleft, ← Category.assoc, h, hone]
  have hinj : Function.Injective pt' := by
    intro e e' hee
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [← hleft, ← hleft, hee]
    · rw [Over.w, Over.w]
  have hfa : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp (algebraMap Ω (DualNumber Ω)) = RingHom.id Ω := by
    ext r
    simp
  have honto : ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) v → ∃ e, pt' e = v := by
    intro v hv
    have hw : v.left ≫ Y.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f := by
      rw [Over.w]
      simp [GlobalTheory.CompanionTheory.Ar.epsAt]
    obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ 𝔐.m.φ = v.left ∧ L ≫ 𝔐.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom :=
      ⟨_, hpb.1.lift_fst _ _ hw, hpb.1.lift_snd _ _ hw⟩
    have htw : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G 𝔐.ξ (Over.homMk (U := GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) L hL2) := by
      unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hv ⊢
      apply hpb.1.hom_ext
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.m.φ = _
        rw [hL1, hv, hone]
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.t.G.hom = _
        rw [hL2, Over.w]
        show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ 𝔐.ξ = 𝔐.ξ
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    obtain ⟨e, he⟩ := 𝔐.M.onto _ htw
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    rw [hleft, he]
    exact hL1
  have hsmul : ∀ (a : Ω) (e : 𝔐.Li), (pt' (a • e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul a)) ≫ (pt' e).left := by
    intro a e
    rw [hleft, hleft, 𝔐.M.smul, Category.assoc]
  let M' : GlobalTheory.CompanionTheory.Ar.LieModel Y.t.G (𝔐.ξ ≫ 𝔐.f) 𝔐.Li := ⟨pt', htan, hinj, honto, hadd, hsmul⟩
  have hsm : AlgebraicGeometry.Smooth Y.t.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ Y.t.semi
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.exists_ext hsm (𝔐.fn.comp ψ.toRingHom) (Z.ξ₀ ≫ Y.j) (𝔐.ξ ≫ 𝔐.f) hdom'.symm Z.M M'
  refine ⟨𝔐.fn.comp ψ.toRingHom, j, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CptIn.IsTie
  exact ⟨hdom, hcst, hj2, fun e => (hleft (j e)).symm.trans (hj1 e)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
