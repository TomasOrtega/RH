import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

/- English proof (translation)
Rewrite using `[(Chart.isLieComb_iff cv v w).1 h, ← Chart.isTan_iff]`. Use `List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_` and prove the remaining obligations. Introduce `a ha`. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 ha`. Conclude with `Chart.isTan_scale (cv i) ((Chart.isTan_iff _).2 (hv i))`.
-/
theorem isTangent_of_isLieComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {cv : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (hv : ∀ i, IsTangent (v i)) (h : IsLieComb cv v w) :
    IsTangent w := by
  rw [(Chart.isLieComb_iff cv v w).1 h, ← Chart.isTan_iff]
  refine List.prod_induction Chart.IsTan (fun a b ha hb => Chart.isTan_mul ha hb) Chart.isTan_one ?_
  intro a ha
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
  exact Chart.isTan_scale (cv i) ((Chart.isTan_iff _).2 (hv i))

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ`. Take `⟨v, hv, hb, -⟩` from `M.lie R f Λ.t' Λ.m2`. Establish `key : ∀ cv w, Λ.Vec cv w ↔ ∃ u', IsLieComb cv v u' ∧ u'.left ≫ Λ.m1.φ = w`. Introduce `cv w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨v', u', h1, h2, h3⟩`. Establish `e : v' = v` using `funext fun j => Chart.inj_over Λ.m2.cart ((h1 j).trans (hv j).symm)`. Conclude with `⟨u', e ▸ h2, h3⟩`. Introduce and unpack `⟨u', h2, h3⟩`. Conclude with `⟨v, u', hv, h2, h3⟩`.

Use `⟨fun cv => ?_, fun cv w h => ?_, fun w hw => ?_⟩` and prove the remaining obligations. Use `⟨(Chart.prodPts cv v).left ≫ Λ.m1.φ, (key _ _).2 ⟨_, (Chart.isLieComb_iff cv v _).2 rfl, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨u', h2, h3⟩` from `(key _ _).1 hw`. Rewrite using `[← h3, (Chart.isLieComb_iff cv v _).1 h2]`.

Take `⟨u', h2, rfl⟩` from `(key _ _).1 h`. Use `⟨?_, (Chart.tan_push Λ.m1.cart u').1 (isTangent_of_isLieComb hb.1 h2)⟩` and prove the remaining obligations. Establish `e1 : Λ.m1.φ ≫ Xo.univ.t.G.hom = Λ.t'.G.hom ≫ x` using `Λ.m1.cart.1.w`. Establish `e2 : u'.left ≫ Λ.t'.G.hom = spMap (algebraMap R (DualNumber R))` using `Over.w u'`. Rewrite using `[Category.assoc, e1, ← Category.assoc, e2]`.

Set `u' : epsR R ⟶ Λ.t'.G` to `Over.homMk (Λ.m1.cart.1.lift w (spMap (algebraMap R (DualNumber R))) hw.1) (Λ.m1.cart.1.lift_snd _ _ _)`. Establish `hu : u'.left ≫ Λ.m1.φ = w` using `Λ.m1.cart.1.lift_fst _ _ _`. Establish `ht : IsTangent u'` using `(Chart.tan_push Λ.m1.cart u').2 (by`. Use `hw.2` as an intermediate fact. Rewrite `this` using `[← hu]`.

Conclude with `this)`. Take `⟨cv, hc, huniq⟩` from `hb.2 u' ht`. Use `⟨cv, (key _ _).2 ⟨u', hc, hu⟩, fun cv' h' => ?_⟩` and prove the remaining obligations. Take `⟨u'', h2, h3⟩` from `(key _ _).1 h'`. Establish `e : u'' = u'` using `Chart.inj_over Λ.m1.cart (h3.trans hu.symm)`.

Conclude with `huniq cv' (e ▸ h2)`.
-/
theorem vec_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), (∀ cv, ∃! w, Λ.Vec cv w) ∧ (∀ cv w, Λ.Vec cv w → IsTanAt x w) ∧ ∀ w, IsTanAt x w → ∃! cv, Λ.Vec cv w := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ
  obtain ⟨v, hv, hb, -⟩ := M.lie R f Λ.t' Λ.m2
  have key : ∀ cv w, Λ.Vec cv w ↔ ∃ u', IsLieComb cv v u' ∧ u'.left ≫ Λ.m1.φ = w := by
    intro cv w
    constructor
    · rintro ⟨v', u', h1, h2, h3⟩
      have e : v' = v := funext fun j => Chart.inj_over Λ.m2.cart ((h1 j).trans (hv j).symm)
      exact ⟨u', e ▸ h2, h3⟩
    · rintro ⟨u', h2, h3⟩
      exact ⟨v, u', hv, h2, h3⟩
  refine ⟨fun cv => ?_, fun cv w h => ?_, fun w hw => ?_⟩
  · refine ⟨(Chart.prodPts cv v).left ≫ Λ.m1.φ, (key _ _).2 ⟨_, (Chart.isLieComb_iff cv v _).2 rfl, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨u', h2, h3⟩ := (key _ _).1 hw
    rw [← h3, (Chart.isLieComb_iff cv v _).1 h2]
  · obtain ⟨u', h2, rfl⟩ := (key _ _).1 h
    refine ⟨?_, (Chart.tan_push Λ.m1.cart u').1 (isTangent_of_isLieComb hb.1 h2)⟩
    have e1 : Λ.m1.φ ≫ Xo.univ.t.G.hom = Λ.t'.G.hom ≫ x := Λ.m1.cart.1.w
    have e2 : u'.left ≫ Λ.t'.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w u'
    rw [Category.assoc, e1, ← Category.assoc, e2]
  · let u' : epsR R ⟶ Λ.t'.G :=
      Over.homMk (Λ.m1.cart.1.lift w (spMap (algebraMap R (DualNumber R))) hw.1) (Λ.m1.cart.1.lift_snd _ _ _)
    have hu : u'.left ≫ Λ.m1.φ = w := Λ.m1.cart.1.lift_fst _ _ _
    have ht : IsTangent u' := (Chart.tan_push Λ.m1.cart u').2 (by
      have := hw.2
      rw [← hu] at this
      exact this)
    obtain ⟨cv, hc, huniq⟩ := hb.2 u' ht
    refine ⟨cv, (key _ _).2 ⟨u', hc, hu⟩, fun cv' h' => ?_⟩
    obtain ⟨u'', h2, h3⟩ := (key _ _).1 h'
    have e : u'' = u' := Chart.inj_over Λ.m1.cart (h3.trans hu.symm)
    exact huniq cv' (e ▸ h2)

end GlobalTheory.Reg
