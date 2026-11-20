import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotSurjectiveSplitTorus

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDataChecks

open GlobalTheory.ChartCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hp` using `isGrpPullback_pullback t.G x0`. Set `φ` to `pullback.fst t.G.hom x0`. Set `up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 → (epsR S ⟶ (Over.pullback x0).obj t.G)` to `fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)`. Establish `hup : ∀ w h, (up w h).left ≫ φ = w` using `fun w h => pullback.lift_fst _ _ _`. Establish `inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v` using `fun h => Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))`.

Establish `one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left` using `fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))`. Establish `tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ)` using `fun w => by`. Establish `e : (1 : Chart.sp (R₀` using `S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left := (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))`. Rewrite using `[← Chart.isTan_iff]`. Use `⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)`. Conclude with `(Category.assoc _ _ _).trans (h.2.trans e.symm)`. Establish `pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ = (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left` using `fun u => congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))`. Establish `comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w, IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ)` using `fun c v w => by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩`. Introduce and unpack `⟨u, hu, hw⟩`. Use `⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩` and prove the remaining obligations. Conclude with `(hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)`.

Use `(Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm` and prove the remaining obligations. Conclude with `(Over.w (Chart.spMap (Chart.scaleD (c i)))).symm`. Establish `: u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G)`. Use function extensionality and compare the values at `fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm`.

Conclude with `congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this`. Set `e` to `Fintype.equivFin (Fin n)`. Set `s : Fin (Fintype.card (Fin n)) ≃ Fin n` to `finCongr (Fintype.card_fin n)`. Establish `hB' : IsLieBasis fun i => v (s i)`. Establish `: ∀ (k : ℕ) (hk : k = n), IsLieBasis fun i : Fin k => v (finCongr hk i)`.

Introduce and unpack `_ rfl`. Conclude with `hB`. Conclude with `this _ _`. Use `⟨fun l => (v (s (e l))).left ≫ φ, fun l => (tan _).1 (hB.1 _), fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hu⟩` from `hB'.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))`.

Use `⟨fun l => c (e l), ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `(comb _ _ _).1 hc` as an intermediate fact. Rewrite `this` using `[hup]`. Simplify `this` using `only [e, Equiv.apply_symm_apply]`. Use `hu (fun i => a (e.symm i)) ((comb _ _ _).2 (by` as an intermediate fact.

Rewrite using `[hup]`. Simplify `ha))` using `only [e, Equiv.apply_symm_apply]`. Use function extensionality and compare the values at `l`. Rewrite using `[← this]`. Simplify using the standard rewrite rules.
-/
theorem tanBasis_of_lieBasis {n : ℕ} (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) (hB : IsLieBasis v) :
    ∃ tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left), IsTanBasisG t x0 tg := by
  classical
  have hp := isGrpPullback_pullback t.G x0
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this

  let e := Fintype.equivFin (Fin n)
  let s : Fin (Fintype.card (Fin n)) ≃ Fin n := finCongr (Fintype.card_fin n)
  have hB' : IsLieBasis fun i => v (s i) := by
    have : ∀ (k : ℕ) (hk : k = n), IsLieBasis fun i : Fin k => v (finCongr hk i) := by
      rintro _ rfl; exact hB
    exact this _ _
  refine ⟨fun l => (v (s (e l))).left ≫ φ, fun l => (tan _).1 (hB.1 _), fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB'.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
  refine ⟨fun l => c (e l), ?_, fun a ha => ?_⟩
  · have := (comb _ _ _).1 hc
    rw [hup] at this
    simpa only [e, Equiv.apply_symm_apply] using this
  · have := hu (fun i => a (e.symm i)) ((comb _ _ _).2 (by
      rw [hup]; simpa only [e, Equiv.apply_symm_apply] using ha))
    funext l; rw [← this]; simp

/- English proof (translation)
Use `t.semi.smooth` as an intermediate fact. Establish `: Smooth ((Over.pullback x0).obj t.G).hom` using `smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this`. Take `⟨n, v, hv⟩` from `Chart.exists_isLieBasis _ this`. Conclude with `⟨n, tanBasis_of_lieBasis t x0 v hv⟩`.
-/
theorem premises_met [IsLocalRing S] :
    ∃ (n : ℕ) (tg : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), IsTanBasisG t x0 tg := by
  have := t.semi.smooth
  have : Smooth ((Over.pullback x0).obj t.G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨n, v, hv⟩ := Chart.exists_isLieBasis _ this
  exact ⟨n, tanBasis_of_lieBasis t x0 v hv⟩

end GlobalTheory.ChartDataChecks
