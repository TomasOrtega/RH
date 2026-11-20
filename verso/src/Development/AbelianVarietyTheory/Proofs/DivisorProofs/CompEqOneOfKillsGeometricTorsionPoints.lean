import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Establish `hA` using `A.ab`. Establish `hC` using `C.ab`. Use `hA.proper` as an intermediate fact. Use `hC.proper` as an intermediate fact. Use `hA.smooth` as an intermediate fact.

Establish `hu : IsUnit (n : Γ(Sp K, ⊤))`. Simplify using `using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom`. Take `⟨_, h3, h4⟩` from `GrpTangent.finiteEtale_mulN_torsion A.X hu`. Establish `hι : torsion.ι A.X n ≫ mulN A.X n = 1`. Rewrite using `[Hom.one_def]`.

Conclude with `pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))`. Use `set L := AlgebraicClosure K`. Use `set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht`. Set `P` to `(Over.pullback t).obj (torsion A.X n)`. Set `C'` to `(Over.pullback t).obj C.X`.

Establish `hP : Etale P.hom`. Express the relevant statement in the definitionally equal form `Etale (pullback.snd (torsion A.X n).hom t)`. Use `infer_instance`. Establish `hPf : LocallyOfFiniteType P.hom`. Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)`.

Use `infer_instance`. Establish `hC' : IsProper C'.hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.snd C.X.hom t)`. Use `infer_instance`. Establish `hPr : IsReduced P.left` using `isReduced_of_smooth_of_isReduced P.hom`.

Establish `hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t = pullback.fst (torsion A.X n).hom t ≫ g.left` using `fun g => by`. Simplify using the standard rewrite rules. Conclude with `pullback.lift_fst _ _ _`. Establish `hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) = (Over.pullback t).map (1 : torsion A.X n ⟶ C.X)`. Use `TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_` and prove the remaining obligations.

Set `z : Sp L ⟶ (torsion A.X n).left` to `y.left ≫ pullback.fst (torsion A.X n).hom t`. Establish `hz : z ≫ (torsion A.X n).hom = t`. Establish `e1 : y.left ≫ P.hom = 𝟙 _`. Express the relevant statement in the definitionally equal form `y.left ≫ pullback.snd (torsion A.X n).hom t = _`. Simplify using `using Over.w y`.

Simplify using `only [z, Category.assoc, pullback.condition]`. Rewrite using `[← Category.assoc]`. Express the relevant statement in the definitionally equal form `(y.left ≫ P.hom) ≫ t = t`. Rewrite using `[e1, Category.id_comp]`. Set `z' : ptOver K L ⟶ torsion A.X n` to `Over.homMk z hz`.

Establish `hw : (z' ≫ torsion.ι A.X n) ^ n = 1`. Rewrite using `[← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]`. Establish `hk` using `hker (z' ≫ torsion.ι A.X n) hw`. Establish `hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X)`. Rewrite using `[MonObj.comp_one, ← Category.assoc, hk]`.

Establish `hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left` using `congrArg CommaMorphism.left hk'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, Category.assoc, hfst]`. Simplify `hkl` using `[z]`.

Establish `w1` using `Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))`. Establish `w2` using `Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))`. Express the relevant statement in the definitionally equal form `_ ≫ pullback.snd C.X.hom t = _ at w1 w2`. Rewrite using `[w1, w2]`. Establish `hred : IsReduced (torsion A.X n).left` using `isReduced_of_smooth_of_isReduced (torsion A.X n).hom`.

Establish `hdom : IsDominant (pullback.fst (torsion A.X n).hom t)` using `inferInstance`. Establish `h6 : torsion.ι A.X n ≫ f.hom = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_` and prove the remaining obligations. Rewrite using `[← hfst, ← hfst, hEq]`.

Establish `e : x ≫ mulN A.X n = toUnit T ≫ η[A.X]` using `by rw [GrpTangent.comp_mulN, hx, Hom.one_def]`. Take `⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x` from `⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩`. Rewrite using `[← e', Category.assoc, h6, MonObj.comp_one]`.
-/
theorem comp_hom_eq_one_of_torsion_pts (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ)
    (hn : (n : K) ≠ 0) (hker : ∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1)
    (T : Over (Sp K)) (x : T ⟶ A.X) (hx : x ^ n = 1) : x ≫ f.hom = 1 := by
  have hA := A.ab
  have hC := C.ab
  have := hA.proper
  have := hC.proper
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨_, h3, h4⟩ := GrpTangent.finiteEtale_mulN_torsion A.X hu
  have hι : torsion.ι A.X n ≫ mulN A.X n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ η[A.X]) (toUnit_unique _ _))
  set L := AlgebraicClosure K
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let P := (Over.pullback t).obj (torsion A.X n)
  let C' := (Over.pullback t).obj C.X
  have hP : Etale P.hom := by
    change Etale (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hPf : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.snd (torsion A.X n).hom t)
    infer_instance
  have hC' : IsProper C'.hom := by
    change IsProper (pullback.snd C.X.hom t)
    infer_instance
  have hPr : IsReduced P.left := isReduced_of_smooth_of_isReduced P.hom
  have hfst : ∀ g : torsion A.X n ⟶ C.X, ((Over.pullback t).map g).left ≫ pullback.fst C.X.hom t =
      pullback.fst (torsion A.X n).hom t ≫ g.left := fun g => by
    simp
    exact pullback.lift_fst _ _ _
  have hEq : (Over.pullback t).map (torsion.ι A.X n ≫ f.hom) =
      (Over.pullback t).map (1 : torsion A.X n ⟶ C.X) := by
    refine TorsionDivisible.hom_ext_of_rationalPoints _ _ fun y => ?_
    let z : Sp L ⟶ (torsion A.X n).left := y.left ≫ pullback.fst (torsion A.X n).hom t
    have hz : z ≫ (torsion A.X n).hom = t := by
      have e1 : y.left ≫ P.hom = 𝟙 _ := by
        change y.left ≫ pullback.snd (torsion A.X n).hom t = _
        simpa using Over.w y
      simp only [z, Category.assoc, pullback.condition]
      rw [← Category.assoc]
      change (y.left ≫ P.hom) ≫ t = t
      rw [e1, Category.id_comp]
    let z' : ptOver K L ⟶ torsion A.X n := Over.homMk z hz
    have hw : (z' ≫ torsion.ι A.X n) ^ n = 1 := by
      rw [← GrpTangent.comp_mulN, Category.assoc, hι, MonObj.comp_one]
    have hk := hker (z' ≫ torsion.ι A.X n) hw
    have hk' : z' ≫ (torsion.ι A.X n ≫ f.hom) = z' ≫ (1 : torsion A.X n ⟶ C.X) := by
      rw [MonObj.comp_one, ← Category.assoc, hk]
    have hkl : z ≫ (torsion.ι A.X n ≫ f.hom).left = z ≫ (1 : torsion A.X n ⟶ C.X).left :=
      congrArg CommaMorphism.left hk'
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, hfst]
      simpa [z] using hkl
    · have w1 := Over.w (y ≫ (Over.pullback t).map (torsion.ι A.X n ≫ f.hom))
      have w2 := Over.w (y ≫ (Over.pullback t).map (1 : torsion A.X n ⟶ C.X))
      change _ ≫ pullback.snd C.X.hom t = _ at w1 w2
      rw [w1, w2]
  have hred : IsReduced (torsion A.X n).left := isReduced_of_smooth_of_isReduced (torsion A.X n).hom
  have hdom : IsDominant (pullback.fst (torsion A.X n).hom t) := inferInstance
  have h6 : torsion.ι A.X n ≫ f.hom = 1 := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated C.X.hom (by rw [Over.w, Over.w]) (pullback.fst (torsion A.X n).hom t) ?_
    rw [← hfst, ← hfst, hEq]
  have e : x ≫ mulN A.X n = toUnit T ≫ η[A.X] := by rw [GrpTangent.comp_mulN, hx, Hom.one_def]
  obtain ⟨y, e'⟩ : ∃ y : T ⟶ torsion A.X n, y ≫ torsion.ι A.X n = x :=
    ⟨pullback.lift x (toUnit T) e, pullback.lift_fst _ _ _⟩
  rw [← e', Category.assoc, h6, MonObj.comp_one]

end GlobalTheory.AV.AbVar

end
