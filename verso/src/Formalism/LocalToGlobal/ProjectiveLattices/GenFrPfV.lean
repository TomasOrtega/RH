import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gfpActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a

/- English proof (translation)
Establish `: IsMonHom (Iso.refl Xo.univ.t.G).hom` using `by dsimp only [Iso.refl]; infer_instance`. Conclude with `(isGrpPullback_of_iso (Iso.refl Xo.univ.t.G)).congr rfl (Over.id_left _)`.
-/
theorem gfp_hcId : IsGrpPullback Xo.univ.t.G Xo.univ.t.G (𝟙 Xo.X) (𝟙 Xo.univ.t.G.left) := by
  have : IsMonHom (Iso.refl Xo.univ.t.G).hom := by dsimp only [Iso.refl]; infer_instance
  exact (isGrpPullback_of_iso (Iso.refl Xo.univ.t.G)).congr rfl (Over.id_left _)

def gfpVec {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x

section V

variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

/- English proof (translation)
Establish `hw : (tvec (x` using `xc) cc).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) := by`. Simplify using `using Over.w (tvec (x := xc) cc)`. Simplify using `only [gfpVec, Category.assoc, pullback.condition, reassoc_of% hw]`.
-/
theorem gfpVec_w (cc : Fin n → L) :
    gfpVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have hw : (tvec (x := xc) cc).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) := by
    simpa using Over.w (tvec (x := xc) cc)
  simp only [gfpVec, Category.assoc, pullback.condition, reassoc_of% hw]

variable (xc) in

def gfpW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gfpVec x xc cc) (gfpVec_w cc)

variable (xc) in
/- English proof (translation)
Use `show gfpVec x xc cc ≫ 𝟙 _ = (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x`. Rewrite using `[Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem gfp_rel (cc : Fin n → L) :
    Rel (F := 𝟙 Xo.univ.t.G.left) x x
      (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) (tvec (x := xc) cc) := by
  show gfpVec x xc cc ≫ 𝟙 _ = (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x
  rw [Category.comp_id]
  rfl

/- English proof (translation)
Use `⟨gfpVec_w cc, ?_⟩` and prove the remaining obligations. Establish `h1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x` using `xc) cc = 1 := ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc`. Establish `e1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x` using `xc) cc).left = (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left := by`. Rewrite using `[h1]`. Establish `e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) L) 1).left = (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by`.

Rewrite using `[map_one]`. Express the relevant statement in the definitionally equal form `(1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫ pullback.fst Xo.univ.t.G.hom x = _ at e2`. Use `show spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ ((tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x) = _`. Rewrite using `[← Category.assoc]`. Express the relevant statement in the definitionally equal form `(ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x = _`.

Rewrite using `[e1, e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']`. Simplify using the standard rewrite rules.
-/
theorem gfp_tan (hx : IsUnivChart _ n xc) (cc : Fin n → L) : IsTanAt x (gfpVec x xc cc) := by
  refine ⟨gfpVec_w cc, ?_⟩
  have h1 : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc = 1 := ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc
  have e1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc).left =
      (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left := by
    rw [h1]
  have e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) 1).left =
      (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by
    rw [map_one]
  change (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
    pullback.fst Xo.univ.t.G.hom x = _ at e2
  show spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ ((tvec (x := xc) cc).left ≫
    pullback.fst Xo.univ.t.G.hom x) = _
  rw [← Category.assoc]
  change (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x = _
  rw [e1, e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
  simp

/- English proof (translation)
Take `⟨hw1, hw2⟩` from `hw`. Set `y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` to `L) (DualNumber L) ⟶ (Over.pullback x).obj Xo.univ.t.G := Over.homMk (pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) (pullback.lift_snd _ _ hw1)`. Establish `e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) L) 1).left = (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by`. Rewrite using `[map_one]`. Express the relevant statement in the definitionally equal form `(1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫ pullback.fst Xo.univ.t.G.hom x = _ at e2`.

Establish `e3 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫ pullback.fst Xo.univ.t.G.hom x = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by`. Rewrite using `[e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']`. Simplify using the standard rewrite rules. Establish `hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y` using `by show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y = 1`. Use `ext`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[e3]`. Express the relevant statement in the definitionally equal form `(spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) ≫ pullback.fst Xo.univ.t.G.hom x = _`. Rewrite using `[Category.assoc, pullback.lift_fst]`. Conclude with `hw2`.

Establish `a1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y).left ≫ pullback.snd Xo.univ.t.G.hom x = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) L).hom := by`. Simplify using `using Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y)`. Establish `a2 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫ pullback.snd Xo.univ.t.G.hom x = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by`. Simplify using `using Over.w (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G)`. Rewrite using `[a1, a2]`.

Use `⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy, ?_⟩` and prove the remaining obligations. Establish `e : y = tvec (x` using `xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy) := by first`. Consider the case `exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx y hy`. Consider the case `exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec y hy`. Use `show w = (tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy)).left ≫ pullback.fst Xo.univ.t.G.hom x`.

Rewrite using `[← e]`. Conclude with `(pullback.lift_fst _ _ _).symm`.
-/
theorem gfp_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gfpVec x xc cc := by
  obtain ⟨hw1, hw2⟩ := hw
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L) ⟶ (Over.pullback x).obj Xo.univ.t.G :=
    Over.homMk (pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) (pullback.lift_snd _ _ hw1)
  have e2 : (pushHom (isGrpPullback_pullback Xo.univ.t.G x) (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) 1).left =
      (1 : Over.mk ((ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom ≫ x) ⟶ Xo.univ.t.G).left := by
    rw [map_one]
  change (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
    pullback.fst Xo.univ.t.G.hom x = _ at e2
  have e3 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
      pullback.fst Xo.univ.t.G.hom x = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    rw [e2, ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    simp
  have hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
    show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y = 1
    ext
    apply pullback.hom_ext
    · rw [e3]
      change (spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫
        pullback.lift w (spMap (algebraMap L (DualNumber L))) hw1) ≫ pullback.fst Xo.univ.t.G.hom x = _
      rw [Category.assoc, pullback.lift_fst]
      exact hw2
    · have a1 : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y).left ≫ pullback.snd Xo.univ.t.G.hom x =
          (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ y)
      have a2 : (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G).left ≫
          pullback.snd Xo.univ.t.G.hom x = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L).hom := by
        simpa using Over.w (1 : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L ⟶ (Over.pullback x).obj Xo.univ.t.G)
      rw [a1, a2]
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy, ?_⟩
  have e : y = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy) := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx y hy
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec y hy
  show w = (tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx y hy)).left ≫ pullback.fst Xo.univ.t.G.hom x
  rw [← e]
  exact (pullback.lift_fst _ _ _).symm

/- English proof (translation)
Establish `hw : ∀ c : Fin n → L, (tvec (x` using `xc) c).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) := fun c => by simpa using Over.w (tvec (x := xc) c)`. Establish `h' : (tvec (x` using `xc) c₁).left ≫ pullback.fst Xo.univ.t.G.hom x = (tvec (x := xc) c₂).left ≫ pullback.fst Xo.univ.t.G.hom x := h`. Establish `ht : tvec (x` using `xc) c₁ = tvec (x := xc) c₂ := Over.OverMorphism.ext (pullback.hom_ext h' (by rw [hw, hw]))`. Use `first`. Consider the case `exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht`.

Consider the case `exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht`.
-/
theorem gfp_inj (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : gfpVec x xc c₁ = gfpVec x xc c₂) : c₁ = c₂ := by
  have hw : ∀ c : Fin n → L,
      (tvec (x := xc) c).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) :=
    fun c => by simpa using Over.w (tvec (x := xc) c)
  have h' : (tvec (x := xc) c₁).left ≫ pullback.fst Xo.univ.t.G.hom x =
      (tvec (x := xc) c₂).left ≫ pullback.fst Xo.univ.t.G.hom x := h
  have ht : tvec (x := xc) c₁ = tvec (x := xc) c₂ :=
    Over.OverMorphism.ext (pullback.hom_ext h' (by rw [hw, hw]))
  first
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff hx]`. Conclude with `ReciprocityTheory.ChartRestriction.G.Chart.eig_iff gfp_hcId (Xo.univ.t.act.act a) (Xo.univ.t.act.act a) (by rw [Category.comp_id, Category.id_comp]) _ (gfp_rel xc cc)`.
-/
theorem gfp_eig_iff [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gfpVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
  refine forall_congr' fun a => ?_
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff hx]
  exact ReciprocityTheory.ChartRestriction.G.Chart.eig_iff gfp_hcId (Xo.univ.t.act.act a) (Xo.univ.t.act.act a)
    (by rw [Category.comp_id, Category.id_comp]) _ (gfp_rel xc cc)

/- English proof (translation)
Establish `h0 : tvec (x` using `xc) (0 : Fin n → L) = 1 := by`. Establish `e0` using `ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0`. Rewrite `e0` using `[add_zero]`. Simplify using `using e0.symm`. Proceed by induction on `m with`.

Consider the case `zero => simp [h0]`. Consider the case `succ m ih`. Rewrite using `[List.ofFn_succ, List.prod_cons, ← ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]`.
-/
theorem gfp_tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  have h0 : tvec (x := xc) (0 : Fin n → L) = 1 := by
    have e0 := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at e0
    simpa using e0.symm
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ← ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]

/- English proof (translation)
Establish `hg : x ≫ 𝟙 Xo.X = x` using `Category.comp_id x`. Set `W' : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` to `L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j => liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫ (gfpW xc (e j) : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G)`. Establish `hW' : ∀ j, Rel (F` using `𝟙 Xo.univ.t.G.left) x x (W' j) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) := fun j => ReciprocityTheory.ChartRestriction.G.Chart.rel_pre _ (gfp_rel xc (e j))`. Establish `hP` using `ReciprocityTheory.ChartRestriction.G.Chart.rel_prod gfp_hcId hg W' _ hW'`. Rewrite `hP` using `[← gfp_tvec_sum hx a e]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hprod⟩`. Establish `eu' : u = W'` using `funext fun j => Over.OverMorphism.ext (hu j)`. Establish `eu : (List.ofFn W').prod = (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀` using `L) (DualNumber L)) ⟶ Xo.univ.t.G) := by`. Rewrite using `[← eu']`.

Conclude with `Over.OverMorphism.ext hprod`. Rewrite `hP` using `[eu]`. Conclude with `ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_v (gfp_rel xc cc) hP)`. Introduce `h`. Substitute `h` using the available equality.

Use `⟨W', fun j => rfl, ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun q => q.left) (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_w gfp_hcId hP (gfp_rel xc _))`.
-/
theorem gfp_comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gfpVec x xc (e j)) a (gfpVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hg : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W' : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫
      (gfpW xc (e j) : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G)
  have hW' : ∀ j, Rel (F := 𝟙 Xo.univ.t.G.left) x x (W' j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => ReciprocityTheory.ChartRestriction.G.Chart.rel_pre _ (gfp_rel xc (e j))
  have hP := ReciprocityTheory.ChartRestriction.G.Chart.rel_prod gfp_hcId hg W' _ hW'
  rw [← gfp_tvec_sum hx a e] at hP
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext (hu j)
    have eu : (List.ofFn W').prod =
        (gfpW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := by
      rw [← eu']
      exact Over.OverMorphism.ext hprod
    rw [eu] at hP
    exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_v (gfp_rel xc cc) hP)
  · intro h
    subst h
    refine ⟨W', fun j => rfl, ?_⟩
    exact congrArg (fun q => q.left) (ReciprocityTheory.ChartRestriction.G.Chart.rel_uniq_w gfp_hcId hP (gfp_rel xc _))

end V

end Formalism.L2.Pj
