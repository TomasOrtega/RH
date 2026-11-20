import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowAct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauBalBox

/- English proof (translation)
Apply `p.lim.hom_ext` to reduce the goal to its premises. Introduce and unpack `⟨i⟩`. Use `first`. Consider the case `exact h i`. Consider the case `simpa using h i`.
-/
private theorem hom_ext_of_isPowGrp_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  apply p.lim.hom_ext
  rintro ⟨i⟩
  first
  | exact h i
  | simpa using h i

/- English proof (translation)
Introduce `hG R _ _ j D D' pD O _ _ _ _ hxe oa`. Take `⟨⟨oB, hros⟩, hc, htau⟩` from `oa`. Use `letI := D.P.isAb.comm`. Use `letI := D'.P.isAb.comm`. Take `⟨r', hr'⟩` from `(GlobalTheory.exists_powAct _ D'.P.A D.P.A j pD.pw).1 O oB`.

Establish `hros' : ∀ a : O, RosatiAdj D'.P.A D'.P.L (r'.act a) (r'.act (star a))` using `fun a => GlobalTheory.rosatiAdj_pow _ D'.P.A D.P.A j pD.pw D.P.L D'.P.L D.P.isLB D'.P.isLB ⟨pD.w, pD.w_gen⟩ (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) (hr' a) (hr' (star a)) (hros a)`. Establish `hc' : ∀ (a : O) (y : D'.X), D'.c (a • y) = D'.c y ≫ r'.act a`. Introduce `a y`. Apply `hom_ext_of_isPowGrp_pr pD.pw` to reduce the goal to its premises. Introduce `i`.

Rewrite using `[pD.c_pr, Category.assoc, hr' a i, ← Category.assoc, pD.c_pr, hxe, Pi.smul_apply, hc]`. Establish `htau' : ∀ a : O, D'.TauBal (r'.act a) (r'.act (star a)) (fun y => a • y) fun y => star a • y`. Introduce `a`. Use `haveI := oB.hom a`. Use `haveI := oB.hom (star a)`.

Use `haveI := r'.hom a`. Use `haveI := r'.hom (star a)`. Conclude with `tauBal_pow hG R j D D' pD (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) inferInstance inferInstance inferInstance inferInstance (hr' a) (hr' (star a)) (hros a) (fun y => a • y) (fun y => star a • y) (fun y => a • y) (fun y => star a • y) (fun x i => by simp only [hxe, …`. Conclude with `⟨⟨⟨r', hros'⟩, hc', htau'⟩, hr'⟩`.
-/
theorem exists_pow_oAct : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a := by
  intro hG R _ _ j D D' pD O _ _ _ _ hxe oa
  obtain ⟨⟨oB, hros⟩, hc, htau⟩ := oa
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨r', hr'⟩ := (GlobalTheory.exists_powAct _ D'.P.A D.P.A j pD.pw).1 O oB
  have hros' : ∀ a : O, RosatiAdj D'.P.A D'.P.L (r'.act a) (r'.act (star a)) := fun a =>
    GlobalTheory.rosatiAdj_pow _ D'.P.A D.P.A j pD.pw D.P.L D'.P.L D.P.isLB D'.P.isLB ⟨pD.w, pD.w_gen⟩
      (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) (hr' a) (hr' (star a)) (hros a)
  have hc' : ∀ (a : O) (y : D'.X), D'.c (a • y) = D'.c y ≫ r'.act a := by
    intro a y
    apply hom_ext_of_isPowGrp_pr pD.pw
    intro i
    rw [pD.c_pr, Category.assoc, hr' a i, ← Category.assoc, pD.c_pr, hxe, Pi.smul_apply, hc]
  have htau' : ∀ a : O, D'.TauBal (r'.act a) (r'.act (star a)) (fun y => a • y) fun y => star a • y := by
    intro a
    haveI := oB.hom a
    haveI := oB.hom (star a)
    haveI := r'.hom a
    haveI := r'.hom (star a)
    exact tauBal_pow hG R j D D' pD (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a))
      inferInstance inferInstance inferInstance inferInstance (hr' a) (hr' (star a)) (hros a)
      (fun y => a • y) (fun y => star a • y) (fun y => a • y) (fun y => star a • y)
      (fun x i => by simp only [hxe, Pi.smul_apply]) (fun x i => by simp only [hxe, Pi.smul_apply])
      (hc a) (hc (star a)) (htau a)
  exact ⟨⟨⟨r', hros'⟩, hc', htau'⟩, hr'⟩

end GlobalTheory.TauBalBox
