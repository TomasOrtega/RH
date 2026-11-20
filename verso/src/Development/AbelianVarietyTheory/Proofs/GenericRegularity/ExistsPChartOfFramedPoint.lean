import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLie

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Reg.ChartInhab

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `and_congr (isGen_iff w) (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl))`.
-/
theorem rigIso_iff {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : RigIso m w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m.cm.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m.cm.e _ (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L)
      (fun _ => rfl))

/- English proof (translation)
Take `⟨w, g, r, -⟩` from `m.lin`. Conclude with `⟨w, g, r⟩`.
-/
theorem exists_rigIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    ∃ w, RigIso m w := by
  obtain ⟨w, g, r, -⟩ := m.lin
  exact ⟨w, g, r⟩

/- English proof (translation)
Substitute `hx` using the available equality. Set `n : CubeMap t''.G t.G` to `{ F := m'.cm.F ≫ m.cm.F, F3 := m'.cm.F3 ≫ m.cm.F3, e := m'.cm.e ≫ m.cm.e e_comm := by rw [← Category.assoc, m'.cm.e_comm, Category.assoc, m.cm.e_comm, Category.assoc] psum_comm := fun I => by`. Rewrite using `[← Category.assoc, m'.cm.psum_comm, Category.assoc, m.cm.psum_comm, Category.assoc] }`. Establish `hb : n.e = g ≫ f` using `by show m'.cm.e ≫ m.cm.e = g ≫ f`. Rewrite using `[m'.base, m.base]`.

Establish `ha : ∀ a, (t''.act.act a).left ≫ n.F = n.F ≫ (t.act.act a).left` using `fun a => by show _ ≫ m'.cm.F ≫ m.cm.F = (m'.cm.F ≫ m.cm.F) ≫ _`. Rewrite using `[← Category.assoc, m'.act, Category.assoc, m.act, Category.assoc]`. Set `N : SABMap t'' t (g ≫ f)` to `⟨n, m'.cart.comp m.cart, hb, ha, pullCubComp _ _ _ _ _ _ m.cm m'.cm n _ _ _ _ _ _ rfl rfl rfl m.lin m'.lin⟩`. Take `⟨g1, r1⟩` from `(rigIso_iff m w).1 hw`. Take `⟨g2, r2⟩` from `(rigIso_iff m' w').1 hw'`.

Take `⟨w'', T⟩` from `exists_comp t'.PP.isLB w w' g1 g2 t.PP.isLB t''.PP.isLB`. Conclude with `⟨N, rfl, w'', (rigIso_iff N w'').2 ⟨T.pgen_comp t'.PP.isLB g1 g2, T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) r1 r2⟩, T⟩`.
-/
theorem exists_comp_rig {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m : SABMap t' t f) (m' : SABMap t'' t' g) (x : S'' ⟶ S) (hx : x = g ≫ f)
    {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ)}
    (hw : RigIso m w) (hw' : RigIso m' w') :
    ∃ n : SABMap t'' t x, n.φ = m'.φ ≫ m.φ ∧ ∃ w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ t''.G.left) (y : Y) (j : t.PP.L.ι) (i : t'.PP.L.ι) (k : t''.PP.L.ι),
        m.φ (m'.φ (r y)) ∈ t.PP.L.U j → m'.φ (r y) ∈ t'.PP.L.U i → r y ∈ t''.PP.L.U k →
        gw w'' r y j k = gw w (r ≫ m'.φ) y j i * gw w' r y i k := by
  subst hx
  let n : CubeMap t''.G t.G :=
    { F := m'.cm.F ≫ m.cm.F, F3 := m'.cm.F3 ≫ m.cm.F3, e := m'.cm.e ≫ m.cm.e
      e_comm := by rw [← Category.assoc, m'.cm.e_comm, Category.assoc, m.cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, m'.cm.psum_comm, Category.assoc, m.cm.psum_comm, Category.assoc] }
  have hb : n.e = g ≫ f := by
    show m'.cm.e ≫ m.cm.e = g ≫ f
    rw [m'.base, m.base]
  have ha : ∀ a, (t''.act.act a).left ≫ n.F = n.F ≫ (t.act.act a).left := fun a => by
    show _ ≫ m'.cm.F ≫ m.cm.F = (m'.cm.F ≫ m.cm.F) ≫ _
    rw [← Category.assoc, m'.act, Category.assoc, m.act, Category.assoc]
  let N : SABMap t'' t (g ≫ f) := ⟨n, m'.cart.comp m.cart, hb, ha,
    pullCubComp _ _ _ _ _ _ m.cm m'.cm n _ _ _ _ _ _ rfl rfl rfl m.lin m'.lin⟩
  obtain ⟨g1, r1⟩ := (rigIso_iff m w).1 hw
  obtain ⟨g2, r2⟩ := (rigIso_iff m' w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t'.PP.isLB w w' g1 g2 t.PP.isLB t''.PP.isLB
  exact ⟨N, rfl, w'', (rigIso_iff N w'').2 ⟨T.pgen_comp t'.PP.isLB g1 g2,
    T.pmaps_comp t'.PP.isLB (fun _ => m'.cm.e_comm) r1 r2⟩, T⟩

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Establish `e : (epsMul s).comp (algebraMap V (DualNumber V)) = algebraMap V (DualNumber V)` using `RingHom.ext fun a => by simp [epsMul]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, e]`.
-/
theorem epsMul_alg {V : Type} [CommRing V] (s : V) :
    spMap (epsMul s) ≫ spMap (algebraMap V (DualNumber V)) = spMap (algebraMap V (DualNumber V)) := by
  have e : (epsMul s).comp (algebraMap V (DualNumber V)) = algebraMap V (DualNumber V) :=
    RingHom.ext fun a => by simp [epsMul]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

/- English proof (translation)
Establish `e : (TrivSqZeroExt.fstHom V V V).toRingHom.comp (algebraMap V (DualNumber V)) = RingHom.id V` using `RingHom.ext fun a => by simp`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]`.
-/
theorem fst_alg {V : Type} [CommRing V] :
    spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) = 𝟙 (Sp V) := by
  have e : (TrivSqZeroExt.fstHom V V V).toRingHom.comp (algebraMap V (DualNumber V)) = RingHom.id V :=
    RingHom.ext fun a => by simp
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]

section Lie

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} (m : SABMap G Xo.univ.t x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eps_hom : (epsOver V V).hom = spMap (algebraMap V (DualNumber V)) := rfl

def push : (epsOver V V ⟶ G.G) →* (tEps x ⟶ Xo.univ.t.G) := pushHom m.cart (epsOver V V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem push_left (v : epsOver V V ⟶ G.G) : (push m v).left = v.left ≫ m.φ := rfl

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w v, Over.w v']))`.
-/
theorem left_inj {v v' : epsOver V V ⟶ G.G} (h : v.left ≫ m.φ = v'.left ≫ m.φ) : v = v' :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w v, Over.w v']))

/- English proof (translation)
Assemble the required witnesses or components as `⟨Over.homMk (m.cart.1.lift u _ hu) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩`.
-/
theorem exists_lift (u : Sp (DualNumber V) ⟶ Xo.univ.t.G.left)
    (hu : u ≫ Xo.univ.t.G.hom = spMap (algebraMap V (DualNumber V)) ≫ x) :
    ∃ v : epsOver V V ⟶ G.G, v.left ≫ m.φ = u :=
  ⟨Over.homMk (m.cart.1.lift u _ hu) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

/- English proof (translation)
Establish `e0 : (ptOver V V).hom = 𝟙 _` using `Spec.map_id _`. Establish `e1 : (1 : ptOver V V ⟶ G.G).left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left`. Use `(congrArg (fun q => q.left) (map_one (pushHom m.cart (ptOver V V)))).trans ?_` and prove the remaining obligations. Rewrite using `[Chart.one_left', Chart.one_left']`. Use `show ((ptOver V V).hom ≫ x) ≫ _ = x ≫ _`.

Rewrite using `[e0, Category.id_comp]`. Establish `e2 : (1 : ptOver V V ⟶ G.G).left ≫ G.G.hom = 𝟙 _` using `(Over.w _).trans e0`. Establish `e3 : (spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ v.left) ≫ G.G.hom = 𝟙 _`. Rewrite using `[Category.assoc, Over.w v]`. Conclude with `fst_alg`.

Prove the components needed by the constructor for the conclusion. Introduce `hh`. Use `⟨Over.w (push m v), ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hh, e1]`. Introduce `hh`.

Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hh.2, e1]`. Conclude with `e3.trans e2.symm`.
-/
theorem tan_iff (v : epsOver V V ⟶ G.G) : IsTan v ↔ IsTanAt x (v.left ≫ m.φ) := by
  have e0 : (ptOver V V).hom = 𝟙 _ := Spec.map_id _
  have e1 : (1 : ptOver V V ⟶ G.G).left ≫ m.φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    refine (congrArg (fun q => q.left) (map_one (pushHom m.cart (ptOver V V)))).trans ?_
    rw [Chart.one_left', Chart.one_left']
    show ((ptOver V V).hom ≫ x) ≫ _ = x ≫ _
    rw [e0, Category.id_comp]
  have e2 : (1 : ptOver V V ⟶ G.G).left ≫ G.G.hom = 𝟙 _ := (Over.w _).trans e0
  have e3 : (spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ v.left) ≫ G.G.hom = 𝟙 _ := by
    rw [Category.assoc, Over.w v]
    exact fst_alg
  constructor
  · intro hh
    refine ⟨Over.w (push m v), ?_⟩
    rw [← Category.assoc, hh, e1]
  · intro hh
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hh.2, e1]
    · exact e3.trans e2.symm

/- English proof (translation)
Establish `e : (v ≫ G.act.act a).left ≫ m.φ = (v.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left`. Rewrite using `[Over.comp_left, Category.assoc, m.act a, Category.assoc]`. Rewrite using `[← e, ← Category.assoc]`. Use `⟨fun h => by rw [h], fun h => m.cart.1.hom_ext h ?_⟩` and prove the remaining obligations. Rewrite using `[Over.w, Category.assoc, Over.w v]`.

Conclude with `(epsMul_alg s).symm`.
-/
theorem eig_iff (v : epsOver V V ⟶ G.G) (a : 𝓞 E) (s : V) :
    (v ≫ G.act.act a).left = spMap (epsMul s) ≫ v.left ↔
      (v.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ (v.left ≫ m.φ) := by
  have e : (v ≫ G.act.act a).left ≫ m.φ = (v.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left := by
    rw [Over.comp_left, Category.assoc, m.act a, Category.assoc]
  rw [← e, ← Category.assoc]
  refine ⟨fun h => by rw [h], fun h => m.cart.1.hom_ext h ?_⟩
  rw [Over.w, Category.assoc, Over.w v]
  exact (epsMul_alg s).symm

/- English proof (translation)
Rewrite using `[map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem push_prod {n : ℕ} (u : Fin n → (epsOver V V ⟶ G.G)) :
    (List.ofFn fun i => push m (u i)).prod = push m (List.ofFn u).prod := by
  rw [map_list_prod, List.map_ofFn]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Use `⟨fun i => push m (u i), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[push_left, hu i, Category.assoc]`. Rewrite using `[push_prod, push_left]`.

Introduce and unpack `⟨u, hu, hv⟩ choose u' hu' using fun i => exists_lift m (u i).left (Over.w (u i))`. Establish `e : u = fun i => push m (u' i)` using `funext fun i => Over.OverMorphism.ext (hu' i).symm`. Use `⟨u', fun i => m.cart.1.hom_ext ?_ ?_, left_inj m ?_⟩` and prove the remaining obligations. Rewrite using `[hu', hu, Category.assoc]`. Rewrite using `[Over.w, Category.assoc, Over.w]`.

Conclude with `(epsMul_alg _).symm`. Rewrite using `[← hv, e, push_prod, push_left]`.
-/
theorem comb_iff {n : ℕ} (b : Fin n → (epsOver V V ⟶ G.G)) (a : Fin n → V) (v : epsOver V V ⟶ G.G) :
    IsComb b a v ↔ IsCombAt x (fun i => (b i).left ≫ m.φ) a (v.left ≫ m.φ) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => push m (u i), fun i => ?_, ?_⟩
    · rw [push_left, hu i, Category.assoc]
    · rw [push_prod, push_left]
  · rintro ⟨u, hu, hv⟩
    choose u' hu' using fun i => exists_lift m (u i).left (Over.w (u i))
    have e : u = fun i => push m (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
    refine ⟨u', fun i => m.cart.1.hom_ext ?_ ?_, left_inj m ?_⟩
    · rw [hu', hu, Category.assoc]
    · rw [Over.w, Category.assoc, Over.w]
      exact (epsMul_alg _).symm
    · rw [← hv, e, push_prod, push_left]

end Lie

section Theta

variable {V : Type} [CommRing V] {x : Sp V ⟶ Xo.X} {G : SAB H (Sp V)} (m : SABMap G Xo.univ.t x)

def toGx : G.G.left ⟶ Gx x :=
  (lift (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G)).left

/- English proof (translation)
The claim follows from `congrArg (fun q => q.left) (lift_fst (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x) (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))`.
-/
theorem toGx_fst : toGx m ≫ (fst (Over.mk x) Xo.univ.t.G).left = G.G.hom :=
  congrArg (fun q => q.left) (lift_fst (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))

/- English proof (translation)
The claim follows from `congrArg (fun q => q.left) (lift_snd (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x) (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))`.
-/
theorem toGx_snd : toGx m ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ :=
  congrArg (fun q => q.left) (lift_snd (Over.homMk G.G.hom rfl : Over.mk (G.G.hom ≫ x) ⟶ Over.mk x)
    (Over.homMk m.φ m.cart.1.w : Over.mk (G.G.hom ≫ x) ⟶ Xo.univ.t.G))

/- English proof (translation)
Establish `cond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x` using `(Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm`. Establish `hφ` using `m.cart.1.lift_fst _ _ cond`. Establish `hh` using `m.cart.1.lift_snd _ _ cond`. Use `⟨m.cart.1.lift _ _ cond, hφ, hh, m.cart.1.hom_ext ?_ ?_, FramedBaseChange.pulledGroup_hom_ext _ _ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hφ, toGx_snd, Category.id_comp]`.

Rewrite using `[Category.assoc, hh, toGx_fst, Category.id_comp]`. Rewrite using `[Category.assoc, toGx_snd, Category.id_comp]`. Conclude with `hφ`. Rewrite using `[Category.assoc, toGx_fst, Category.id_comp]`. Conclude with `hh`.
-/
theorem exists_inv : ∃ h : Gx x ⟶ G.G.left, h ≫ m.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
    h ≫ G.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ∧ toGx m ≫ h = 𝟙 _ ∧ h ≫ toGx m = 𝟙 _ := by
  have cond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  have hφ := m.cart.1.lift_fst _ _ cond
  have hh := m.cart.1.lift_snd _ _ cond
  refine ⟨m.cart.1.lift _ _ cond, hφ, hh, m.cart.1.hom_ext ?_ ?_, FramedBaseChange.pulledGroup_hom_ext _ _ ?_ ?_⟩
  · rw [Category.assoc, hφ, toGx_snd, Category.id_comp]
  · rw [Category.assoc, hh, toGx_fst, Category.id_comp]
  · rw [Category.assoc, toGx_snd, Category.id_comp]; exact hφ
  · rw [Category.assoc, toGx_fst, Category.id_comp]; exact hh

/- English proof (translation)
Introduce `y hy` and use `Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) (toGx_snd m)).mpr hy`.
-/
theorem le_toGx (j : Xo.univ.t.PP.L.ι) : m.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ toGx m ⁻¹ᵁ (PPx x).U (fun _ => j) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) (toGx_snd m)).mpr hy

def SecRel (w : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m.φ)) (s : LB.Sec (PPx x)) (τ : LB.Sec G.PP.L) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j k, m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ G.PP.L.U k →
    gs (r ≫ toGx m) z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (τ.f k)

variable {w : LB.Iso G.PP.L (Xo.univ.t.PP.L.pull m.φ)}

/- English proof (translation)
Set `σ : ∀ j, Γ(G.G.left, m.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j)` to `fun j => ((toGx m).appLE _ _ (le_toGx m j)).hom (s.f (fun _ => j))`. Establish `gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j, m.φ (r z) ∈ Xo.univ.t.PP.L.U j → gs r z _ (σ j) = gs (r ≫ toGx m) z _ (s.f (fun _ => j))` using `fun Z r z j hz => gs_appLE (toGx m) _ _ (le_toGx m j) r z hz _`. Take `⟨τ, hτ⟩` from `sec_down hw Xo.univ.t.PP.isLB G.PP.isLB σ fun y j j' h₁ h₂ => by`. Establish `m₁ : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j)` using `le_toGx m j h₁`. Establish `m₂ : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j')` using `le_toGx m j' h₂`.

Establish `gg : gm (𝟙 _ ≫ toGx m) y _ ((PPx x).g (fun _ => j) (fun _ => j')) = gm m.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')` using `(gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1) (𝟙 _ ≫ toGx m) y _ _ m₁ m₂).trans (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, toGx_snd, Category.id_comp])`. Conclude with `(gP _ (𝟙 _) y j h₁).trans ((gs_compat s (𝟙 _ ≫ toGx m) y m₁ m₂).trans (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))`. Conclude with `⟨τ, fun Z r z j k h₁ h₂ => (gP Z r z j h₁).symm.trans (hτ Z r z j k h₁ h₂)⟩`.
-/
theorem exists_down (hw : PGen w) (s : LB.Sec (PPx x)) : ∃ τ, SecRel m w s τ := by
  let σ : ∀ j, Γ(G.G.left, m.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j =>
    ((toGx m).appLE _ _ (le_toGx m j)).hom (s.f (fun _ => j))
  have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.G.left) (z : Z) j, m.φ (r z) ∈ Xo.univ.t.PP.L.U j →
      gs r z _ (σ j) = gs (r ≫ toGx m) z _ (s.f (fun _ => j)) := fun Z r z j hz =>
    gs_appLE (toGx m) _ _ (le_toGx m j) r z hz _
  obtain ⟨τ, hτ⟩ := sec_down hw Xo.univ.t.PP.isLB G.PP.isLB σ fun y j j' h₁ h₂ => by
    have m₁ : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j) := le_toGx m j h₁
    have m₂ : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j') := le_toGx m j' h₂
    have gg : gm (𝟙 _ ≫ toGx m) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
        gm m.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
      (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => 1)
        (𝟙 _ ≫ toGx m) y _ _ m₁ m₂).trans
        (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, toGx_snd, Category.id_comp])
    exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s (𝟙 _ ≫ toGx m) y m₁ m₂).trans
      (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
  exact ⟨τ, fun Z r z j k h₁ h₂ => (gP Z r z j h₁).symm.trans (hτ Z r z j k h₁ h₂)⟩

/- English proof (translation)
Take `⟨h, hφ, -, hg, -⟩` from `exists_inv m`. Take `⟨s1, hs1⟩` from `thf_secUp hw Xo.univ.t.PP.isLB G.PP.isLB τ`. Use `⟨thfPull1 Xo.univ.t.PP.L h hφ s1, fun Z r z j k h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `mg : (r ≫ toGx m) z ∈ (PPx x).U (fun _ => j)` using `le_toGx m j h₁`. Use `(gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (r ≫ toGx m) z mg _).trans ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, hg, Category.comp_id]`. Conclude with `hs1 _ r z (fun _ => j) k (mem_pull.2 h₁) h₂`.
-/
theorem exists_up (hw : PGen w) (τ : LB.Sec G.PP.L) : ∃ s, SecRel m w s τ := by
  obtain ⟨h, hφ, -, hg, -⟩ := exists_inv m
  obtain ⟨s1, hs1⟩ := thf_secUp hw Xo.univ.t.PP.isLB G.PP.isLB τ
  refine ⟨thfPull1 Xo.univ.t.PP.L h hφ s1, fun Z r z j k h₁ h₂ => ?_⟩
  have mg : (r ≫ toGx m) z ∈ (PPx x).U (fun _ => j) := le_toGx m j h₁
  refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (r ≫ toGx m) z mg _).trans ?_
  rw [Category.assoc, hg, Category.comp_id]
  exact hs1 _ r z (fun _ => j) k (mem_pull.2 h₁) h₂

/- English proof (translation)
Take `⟨h, hφ, hh, hg, h0g⟩` from `exists_inv m`. Prove the components needed by the constructor for the conclusion. Introduce `ha k`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart Xo.univ.t.PP.isLB (m.φ y)`.

Establish `mg : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j)` using `le_toGx m j hj`. Establish `e1` using `h₂ _ (𝟙 _) y j k hj hy`. Establish `e2 : gs (𝟙 _ ≫ toGx m) y _ (s'.f (fun _ => j)) = cst (𝟙 _ ≫ G.G.hom) y a * ((gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (τ.f k))`. Rewrite using `[ha (fun _ => j), gs_mul _ y _ mg]`. Use `congrArg₂ (· * ·) ?_ (h₁ _ (𝟙 _) y j k hj hy)` and prove the remaining obligations.

Conclude with `(gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ y mg a).trans (by rw [Category.assoc, toGx_fst])`. Rewrite using `[gs_mul _ y _ hy, gs_constFn _ _ _ y hy]`. Rewrite `e2` using `[e1, mul_left_comm]`. Conclude with `(Units.mul_right_inj _).1 e2`. Introduce `ha (i : Fin 1 → Xo.univ.t.PP.L.ι)`.

Take `⟨j, rfl⟩ : ∃ j, i = fun _ => j` from `⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Establish `mφ : m.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j` using `(congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m.φ = (snd (Over.mk x) Xo.univ.t.G).left)).mpr (Set.mem_iInter.1 hy 0)`. Take `⟨k, hk⟩` from `exists_chart G.PP.isLB ((𝟙 _ ≫ h) y)`. Establish `c1 : (𝟙 _ ≫ h) ≫ toGx m = 𝟙 _` using `by rw [Category.id_comp, h0g]`.

Establish `e1 : gs (𝟙 _) y _ (s'.f (fun _ => j)) = (gw w (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ G.G.hom) y a * gs (𝟙 _ ≫ h) y _ (τ.f k))`. Use `(congrArg (fun q => gs q y _ (s'.f (fun _ => j))) c1).symm.trans ?_` and prove the remaining obligations. Use `(h₂ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_)` and prove the remaining obligations. Rewrite using `[ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]`. Establish `e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (τ.f k)` using `(congrArg (fun q => gs q y _ (s.f (fun _ => j))) c1).symm.trans (h₁ _ (𝟙 _ ≫ h) y j k mφ hk)`.

Establish `e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ G.G.hom) y a`. Rewrite using `[show (𝟙 _ ≫ h) ≫ G.G.hom = 𝟙 _ ≫ (fst (Over.mk x) Xo.univ.t.G).left by rw [Category.assoc, hh]]`. Conclude with `gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ (𝟙 _) y hy a`. Conclude with `e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))`.
-/
theorem multiple_iff {s s' : LB.Sec (PPx x)} {τ τ' : LB.Sec G.PP.L} (h₁ : SecRel m w s τ) (h₂ : SecRel m w s' τ')
    (a : V) : (∀ i, s'.f i = scal x a i * s.f i) ↔ ∀ k, τ'.f k = constFn G.G.hom _ a * τ.f k := by
  obtain ⟨h, hφ, hh, hg, h0g⟩ := exists_inv m
  constructor
  · intro ha k
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ y)
    have mg : (𝟙 _ ≫ toGx m) y ∈ (PPx x).U (fun _ => j) := le_toGx m j hj
    have e1 := h₂ _ (𝟙 _) y j k hj hy
    have e2 : gs (𝟙 _ ≫ toGx m) y _ (s'.f (fun _ => j)) =
        cst (𝟙 _ ≫ G.G.hom) y a * ((gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (τ.f k)) := by
      rw [ha (fun _ => j), gs_mul _ y _ mg]
      refine congrArg₂ (· * ·) ?_ (h₁ _ (𝟙 _) y j k hj hy)
      exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ y mg a).trans (by rw [Category.assoc, toGx_fst])
    rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
    rw [e1, mul_left_comm] at e2
    exact (Units.mul_right_inj _).1 e2
  · intro ha (i : Fin 1 → Xo.univ.t.PP.L.ι)
    obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
    refine fn_ext fun y hy => ?_
    have mφ : m.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
        (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m.φ = (snd (Over.mk x) Xo.univ.t.G).left)).mpr
        (Set.mem_iInter.1 hy 0)
    obtain ⟨k, hk⟩ := exists_chart G.PP.isLB ((𝟙 _ ≫ h) y)
    have c1 : (𝟙 _ ≫ h) ≫ toGx m = 𝟙 _ := by rw [Category.id_comp, h0g]
    have e1 : gs (𝟙 _) y _ (s'.f (fun _ => j)) =
        (gw w (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ G.G.hom) y a * gs (𝟙 _ ≫ h) y _ (τ.f k)) := by
      refine (congrArg (fun q => gs q y _ (s'.f (fun _ => j))) c1).symm.trans ?_
      refine (h₂ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_)
      rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
    have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (τ.f k) :=
      (congrArg (fun q => gs q y _ (s.f (fun _ => j))) c1).symm.trans (h₁ _ (𝟙 _ ≫ h) y j k mφ hk)
    have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ G.G.hom) y a := by
      rw [show (𝟙 _ ≫ h) ≫ G.G.hom = 𝟙 _ ≫ (fst (Over.mk x) Xo.univ.t.G).left by rw [Category.assoc, hh]]
      exact gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ (𝟙 _) y hy a
    exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))

end Theta

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce `j hj y z ⟨hx, hu, pm, hs, hf, ha⟩`. Establish `ej : j.toRingHom = algebraMap T.V T.Fr` using `RingHom.ext hj`. Rewrite `hx`, `hu`, `hf` using `[ej]`. Establish `hinj : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective _ _`.

Establish `hio : ∀ r, algebraMap T.V T.Fr (algebraMap c.F T.V r) = io r` using `fun r => (hj _).symm.trans (j.commutes r)`. Choose the witnesses or unpack the hypotheses as in `⟨G, m⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Xo.univ.t y.x) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull y.x Xo.univ.t`. Conclude with `⟨_, ⟨m⟩⟩`. Take `⟨m⟩` from `m`.

Choose the witnesses or unpack the hypotheses as in `⟨t', m2⟩ : ∃ t' : SAB H (Sp T.Fr), Nonempty (SABMap t' G (spMap (algebraMap T.V T.Fr))) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G`. Conclude with `⟨_, ⟨m⟩⟩`. Take `⟨m2⟩` from `m2`. Take `⟨w0, hw0⟩` from `exists_rigIso m`.

Take `⟨w2, hw2⟩` from `exists_rigIso m2`. Take `⟨m1, hm1, w1, hw1, tri⟩` from `exists_comp_rig m m2 z.x hx hw0 hw2`. Establish `g0` using `(isGen_iff w0).1 hw0.1`. Establish `g1` using `(isGen_iff w1).1 hw1.1`. Establish `g2` using `(isGen_iff w2).1 hw2.1`.

Use `⟨G, t', m1, m2, ?_, ?_⟩` and prove the remaining obligations. Use `choose ub hub using fun τ i => exists_lift m (y.u τ i) (y.tan τ i).1`. Establish `eig : ∀ τ v, IsEigV c io G τ v ↔ IsEigAt c τ (v.left ≫ m.φ)` using `fun τ v => ⟨fun h a => (eig_iff m v a _).1 (h a _ (hio _)), fun h a s hs => by`. Take `rfl : s = algebraMap c.F T.V (embK c τ a)` from `hinj (hs.trans (hio _).symm)`. Conclude with `(eig_iff m v a _).2 (h a)⟩`.

Use `⟨ub, fun τ i => (tan_iff m _).2 (hub τ i ▸ y.tan τ i), fun τ i => (eig τ _).2 (hub τ i ▸ y.eig τ i), fun τ v h₁ h₂ => ?_, fun τ i => ?_⟩` and prove the remaining obligations. Establish `e : y.u τ = fun i => (ub τ i).left ≫ m.φ` using `funext fun i => (hub τ i).symm`. Use `y.basis τ _ ((tan_iff m v).1 h₁) ((eig τ v).1 h₂)` as an intermediate fact. Rewrite `this` using `[e]`. Simplify `this` using `only [comb_iff m]`.

Establish `cond : (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ≫ G.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr)`. Rewrite using `[Category.assoc, Over.w (ub τ i), eps_hom, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp]`. Use `congr 1`. Apply the tactic sequence `exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Use `⟨m2.cart.1.lift _ _ cond, ?_, m2.cart.1.lift_fst _ _ cond⟩` and prove the remaining obligations.

Rewrite using `[hm1, ← Category.assoc, m2.cart.1.lift_fst _ _ cond, Category.assoc, hub, hu]`. Take `⟨θ, hθ⟩` from `exists_down m g0 y.s`. Take `⟨σ', hσ'⟩` from `sec_pull_down g2 G.PP.isLB t'.PP.isLB θ`. Take `⟨s1, hs1⟩` from `thf_secUp g1 Xo.univ.t.PP.isLB t'.PP.isLB σ'`. Use `⟨θ, fun σ => ?_, w1, w2, σ', s1, thfPull G.PP.L m2.φ θ, hw1, hw2, ?_, ?_, fun _ _ => rfl, ?_⟩` and prove the remaining obligations.

Take `⟨s, hs⟩` from `exists_up m g0 σ`. Take `⟨a, ha, hu⟩` from `y.gen s`. Conclude with `⟨a, (multiple_iff m hθ hs a).1 ha, fun a' ha' => hu a' ((multiple_iff m hθ hs a').2 ha')⟩`. Conclude with `fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun p hp => (gs_res _ p _ hp _).trans ((hs1 _ (𝟙 _) p i k hp.1 hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))`. Conclude with `fun (i : PUnit → G.PP.L.ι) k => fn_ext fun p hp => (gs_res _ p _ hp _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) p hp.1 _).trans ((hσ' _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ …`.

Introduce `g e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ`. Use `fn_ext fun p hp => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `exists_chart t'.PP.isLB p`. Take `⟨i, hi⟩` from `exists_chart G.PP.isLB (m2.φ p)`. Establish `hp' : m.φ (m2.φ p) ∈ Xo.univ.t.PP.L.U (J PUnit.unit)` using `(congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) hm1).mp (mem_pull.1 hp)`.

Establish `eg : (𝟙 _ ≫ g) ≫ pm = (𝟙 _ ≫ m2.φ) ≫ toGx m`. Rewrite using `[Category.id_comp, Category.id_comp]`. Apply `FramedBaseChange.pulledGroup_hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs, e₁, hm1, Category.assoc, toGx_snd]`. Rewrite using `[Category.assoc, hf, ← Category.assoc, e₂, Category.assoc, toGx_fst]`.

Conclude with `m2.cart.1.w.symm`. Establish `hle` using `FramedBaseChange.chart_le pm hs (fun _ => J PUnit.unit)`. Rewrite using `[hs1 _ (𝟙 _) p J k hp hk, gs_appLE g _ _ hJ (𝟙 _) p hp, ← ha _ hle, gs_appLE pm _ _ hle (𝟙 _ ≫ g) p (hJ hp), eg, hθ _ (𝟙 _ ≫ m2.φ) p _ i hp' hi, hσ' _ (𝟙 _) p i k hi hk, tri _ (𝟙 _) p _ i k hp' hi hk, Units.val_mul, _root_.mul_assoc]`.
-/
theorem integral_of_frMap (T : CDVR) [Algebra c.F T.V] (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (j : T.V →ₐ[c.F] T.Fr), (∀ v, j v = algebraMap T.V T.Fr v) → ∀ (y : FrPt Xo c T.V) (z : FrPt Xo c T.Fr),
      FrMap j y z → Integral T io z := by
  letI := io.toAlgebra
  intro j hj y z ⟨hx, hu, pm, hs, hf, ha⟩
  have ej : j.toRingHom = algebraMap T.V T.Fr := RingHom.ext hj
  rw [ej] at hx hu hf
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  have hio : ∀ r, algebraMap T.V T.Fr (algebraMap c.F T.V r) = io r := fun r => (hj _).symm.trans (j.commutes r)
  obtain ⟨G, m⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Xo.univ.t y.x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y.x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨t', m2⟩ : ∃ t' : SAB H (Sp T.Fr), Nonempty (SABMap t' G (spMap (algebraMap T.V T.Fr))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T.V T.Fr)) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m2⟩ := m2
  obtain ⟨w0, hw0⟩ := exists_rigIso m
  obtain ⟨w2, hw2⟩ := exists_rigIso m2
  obtain ⟨m1, hm1, w1, hw1, tri⟩ := exists_comp_rig m m2 z.x hx hw0 hw2
  have g0 := (isGen_iff w0).1 hw0.1
  have g1 := (isGen_iff w1).1 hw1.1
  have g2 := (isGen_iff w2).1 hw2.1
  refine ⟨G, t', m1, m2, ?_, ?_⟩
  · choose ub hub using fun τ i => exists_lift m (y.u τ i) (y.tan τ i).1
    have eig : ∀ τ v, IsEigV c io G τ v ↔ IsEigAt c τ (v.left ≫ m.φ) := fun τ v =>
      ⟨fun h a => (eig_iff m v a _).1 (h a _ (hio _)), fun h a s hs => by
        obtain rfl : s = algebraMap c.F T.V (embK c τ a) := hinj (hs.trans (hio _).symm)
        exact (eig_iff m v a _).2 (h a)⟩
    refine ⟨ub, fun τ i => (tan_iff m _).2 (hub τ i ▸ y.tan τ i), fun τ i => (eig τ _).2 (hub τ i ▸ y.eig τ i),
      fun τ v h₁ h₂ => ?_, fun τ i => ?_⟩
    · have e : y.u τ = fun i => (ub τ i).left ≫ m.φ := funext fun i => (hub τ i).symm
      have := y.basis τ _ ((tan_iff m v).1 h₁) ((eig τ v).1 h₂)
      rw [e] at this
      simpa only [comb_iff m] using this
    · have cond : (spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ≫ G.G.hom =
          spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
        rw [Category.assoc, Over.w (ub τ i), eps_hom, ← FramedBaseChange.spec_comp, ← FramedBaseChange.spec_comp]
        congr 1
        exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      refine ⟨m2.cart.1.lift _ _ cond, ?_, m2.cart.1.lift_fst _ _ cond⟩
      rw [hm1, ← Category.assoc, m2.cart.1.lift_fst _ _ cond, Category.assoc, hub, hu]
  · obtain ⟨θ, hθ⟩ := exists_down m g0 y.s
    obtain ⟨σ', hσ'⟩ := sec_pull_down g2 G.PP.isLB t'.PP.isLB θ
    obtain ⟨s1, hs1⟩ := thf_secUp g1 Xo.univ.t.PP.isLB t'.PP.isLB σ'
    refine ⟨θ, fun σ => ?_, w1, w2, σ', s1, thfPull G.PP.L m2.φ θ, hw1, hw2, ?_, ?_, fun _ _ => rfl, ?_⟩
    · obtain ⟨s, hs⟩ := exists_up m g0 σ
      obtain ⟨a, ha, hu⟩ := y.gen s
      exact ⟨a, (multiple_iff m hθ hs a).1 ha, fun a' ha' => hu a' ((multiple_iff m hθ hs a').2 ha')⟩
    · exact fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun p hp =>
        (gs_res _ p _ hp _).trans ((hs1 _ (𝟙 _) p i k hp.1 hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))
    · exact fun (i : PUnit → G.PP.L.ι) k => fn_ext fun p hp =>
        (gs_res _ p _ hp _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) p hp.1 _).trans
          ((hσ' _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _))))))
    · intro g e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
      refine fn_ext fun p hp => ?_
      obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB p
      obtain ⟨i, hi⟩ := exists_chart G.PP.isLB (m2.φ p)
      have hp' : m.φ (m2.φ p) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
        (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) hm1).mp (mem_pull.1 hp)
      have eg : (𝟙 _ ≫ g) ≫ pm = (𝟙 _ ≫ m2.φ) ≫ toGx m := by
        rw [Category.id_comp, Category.id_comp]
        apply FramedBaseChange.pulledGroup_hom_ext
        · rw [Category.assoc, hs, e₁, hm1, Category.assoc, toGx_snd]
        · rw [Category.assoc, hf, ← Category.assoc, e₂, Category.assoc, toGx_fst]
          exact m2.cart.1.w.symm
      have hle := FramedBaseChange.chart_le pm hs (fun _ => J PUnit.unit)
      rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE g _ _ hJ (𝟙 _) p hp, ← ha _ hle,
        gs_appLE pm _ _ hle (𝟙 _ ≫ g) p (hJ hp), eg, hθ _ (𝟙 _ ≫ m2.φ) p _ i hp' hi,
        hσ' _ (𝟙 _) p i k hi hk, tri _ (𝟙 _) p _ i k hp' hi hk, Units.val_mul, _root_.mul_assoc]

end GlobalTheory.Reg.ChartInhab

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

end GlobalTheory.Reg
