import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsPullbackAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsLocConst

/- English proof (translation)
Introduce `a b h`. Establish `h'` using `congrArg CommaMorphism.left h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `h'`.

Conclude with `(Over.w a).trans (Over.w b).symm`.
-/
theorem push_injective {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (x : S' ⟶ S) (T : Over S') :
    Function.Injective (pushHom (isGrpPullback_pullback A x) T) := by
  intro a b h
  have h' := congrArg CommaMorphism.left h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h'
  · exact (Over.w a).trans (Over.w b).symm

/- English proof (translation)
Introduce `S A _ hA k _ _ x n hn Z t z hz w`. Establish `hB : IsAbelianScheme ((Over.pullback x).obj A)` using `Out.TLinPf.isAb_pullback x A hA`. Establish `hg` using `isGrpPullback_pullback A x`. Establish `htx : t.left ≫ x = Z.hom` using `Over.w t`. Set `Z' : Over (Sp k)` to `Over.mk t.left`.

Set `z' : Z' ⟶ (Over.pullback x).obj A` to `Over.homMk (pullback.lift z.left t.left ((Over.w z).trans htx.symm)) (pullback.lift_snd _ _ _)`. Set `e : Z ⟶ Over.mk (Z'.hom ≫ x)` to `Over.homMk (𝟙 Z.left) (by show 𝟙 _ ≫ t.left ≫ x = Z.hom`. Rewrite using `[Category.id_comp, htx])`. Set `e' : Over.mk (Z'.hom ≫ x) ⟶ Z` to `Over.homMk (𝟙 Z.left) (by show 𝟙 _ ≫ Z.hom = t.left ≫ x`. Rewrite using `[Category.id_comp, htx])`.

Establish `hee : e' ≫ e = 𝟙 _` using `Over.OverMorphism.ext (by show 𝟙 Z.left ≫ 𝟙 Z.left = 𝟙 Z.left; exact Category.id_comp _)`. Establish `hez : e ≫ pushHom hg Z' z' = z` using `Over.OverMorphism.ext (by show 𝟙 _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = z.left`. Rewrite using `[Category.id_comp, pullback.lift_fst])`. Establish `hz' : z' ^ n = 1`. Apply `push_injective A x Z'` to reduce the goal to its premises.

Rewrite using `[map_pow, map_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, hee, Category.id_comp]`. Use `_ = e' ≫ (e ≫ pushHom hg Z' z') ^ n := by rw [MonObj.comp_pow]`. Use `_ = 1 := by rw [hez, hz, MonObj.comp_one]`.

Establish `hK` using `GlobalTheory.KerConst.isPullback_const_ker k ((Over.pullback x).obj A) hB n hn`. Establish `hcond : z' ≫ 𝟙 _ ^ n = toUnit Z' ≫ η[(Over.pullback x).obj A]`. Rewrite using `[MonObj.comp_pow, Category.comp_id, hz', Hom.one_def]`. Set `g` to `hK.lift z' (toUnit Z') hcond`. Establish `hgz : g ≫ Sigma.desc (fun c => c.1) = z'` using `hK.lift_fst _ _ _`.

Set `P` to `{c : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback x).obj A // c ^ n = 1}`. Set `D : (∐ fun _ : P => 𝟙_ (Over (Sp k))) ⟶ GlobalTheory.PointQuot.constObj (Sp k) P` to `Sigma.desc fun c => GlobalTheory.PointQuot.constPt (Sp k) c`. Establish `hDE : D ≫ GlobalTheory.PointQuot.constDesc (fun c : P => c.1) = Sigma.desc (fun c : P => c.1)` using `Sigma.hom_ext _ _ fun c => by`. Rewrite using `[← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, GlobalTheory.PointQuot.constPt_desc]`. Take `⟨U, hwU, c, hc⟩` from `GlobalTheory.PointQuot.locally_const_desc (fun c : P => c.1) (g ≫ D) w`.

Establish `hU : GlobalTheory.PointQuot.openι Z' U ≫ z' = toUnit _ ≫ c.1`. Rewrite using `[← hc, ← hgz, ← hDE]`. Simplify using `only [Category.assoc]`. Set `y : Over.mk x ⟶ A` to `Over.homMk (c.1.left ≫ pullback.fst A.hom x) (by show (c.1.left ≫ pullback.fst A.hom x) ≫ A.hom = x`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`.

Establish `hc1 : c.1.left ≫ pullback.snd A.hom x = 𝟙 _` using `Over.w c.1`. Rewrite using `[hc1, Category.id_comp])`. Set `e'' : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp k))).hom ≫ x)` to `Over.homMk (𝟙 _) (by show 𝟙 _ ≫ 𝟙 _ ≫ x = x`. Rewrite using `[Category.id_comp, Category.id_comp])`. Establish `hy : y = e'' ≫ pushHom hg _ c.1` using `Over.OverMorphism.ext (by show c.1.left ≫ pullback.fst A.hom x = 𝟙 _ ≫ (c.1.left ≫ pullback.fst A.hom x)`.

Rewrite using `[Category.id_comp])`. Use `⟨GlobalTheory.PointQuot.openObj Z U, GlobalTheory.PointQuot.openι Z U, y, ⟨w, hwU⟩, ?_, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `show IsOpenImmersion U.ι infer_instance`. Rewrite using `[hy, ← MonObj.comp_pow, ← map_pow, c.2, map_one, MonObj.comp_one]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Establish `h1` using `congrArg CommaMorphism.left hU`. Establish `h2 : (toUnit (GlobalTheory.PointQuot.openObj Z' U)).left = U.ι ≫ t.left` using `(Category.comp_id _).symm.trans (Over.w (toUnit (GlobalTheory.PointQuot.openObj Z' U)))`. Use `show U.ι ≫ z.left = U.ι ≫ t.left ≫ c.1.left ≫ pullback.fst A.hom x`. Establish `h3 : z.left = z'.left ≫ pullback.fst A.hom x` using `(pullback.lift_fst _ _ _).symm`. Simplify using `only [Over.comp_left] at h1`.

Rewrite using `[h3, ← Category.assoc]`. Use `erw [h1, h2]`. Conclude with `Category.assoc _ _ _`.
-/
theorem locally_const_torsion :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ (Z : Over S) (t : Z ⟶ Over.mk x) (z : Z ⟶ A), z ^ n = 1 →
      ∀ w : Z.left, ∃ (V : Over S) (i : V ⟶ Z) (y : Over.mk x ⟶ A) (w' : V.left),
        IsOpenImmersion i.left ∧ i.left w' = w ∧ y ^ n = 1 ∧ i ≫ z = i ≫ t ≫ y := by
  intro S A _ hA k _ _ x n hn Z t z hz w
  have hB : IsAbelianScheme ((Over.pullback x).obj A) := Out.TLinPf.isAb_pullback x A hA
  have hg := isGrpPullback_pullback A x
  have htx : t.left ≫ x = Z.hom := Over.w t
  let Z' : Over (Sp k) := Over.mk t.left
  let z' : Z' ⟶ (Over.pullback x).obj A :=
    Over.homMk (pullback.lift z.left t.left ((Over.w z).trans htx.symm)) (pullback.lift_snd _ _ _)
  let e : Z ⟶ Over.mk (Z'.hom ≫ x) := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ t.left ≫ x = Z.hom
    rw [Category.id_comp, htx])
  let e' : Over.mk (Z'.hom ≫ x) ⟶ Z := Over.homMk (𝟙 Z.left) (by
    show 𝟙 _ ≫ Z.hom = t.left ≫ x
    rw [Category.id_comp, htx])
  have hee : e' ≫ e = 𝟙 _ := Over.OverMorphism.ext (by show 𝟙 Z.left ≫ 𝟙 Z.left = 𝟙 Z.left; exact Category.id_comp _)
  have hez : e ≫ pushHom hg Z' z' = z := Over.OverMorphism.ext (by
    show 𝟙 _ ≫ (pullback.lift _ _ _ ≫ pullback.fst _ _) = z.left
    rw [Category.id_comp, pullback.lift_fst])
  have hz' : z' ^ n = 1 := by
    apply push_injective A x Z'
    rw [map_pow, map_one]
    calc (pushHom hg Z' z') ^ n = e' ≫ e ≫ (pushHom hg Z' z') ^ n := by
          rw [← Category.assoc, hee, Category.id_comp]
      _ = e' ≫ (e ≫ pushHom hg Z' z') ^ n := by rw [MonObj.comp_pow]
      _ = 1 := by rw [hez, hz, MonObj.comp_one]
  have hK := GlobalTheory.KerConst.isPullback_const_ker k ((Over.pullback x).obj A) hB n hn
  have hcond : z' ≫ 𝟙 _ ^ n = toUnit Z' ≫ η[(Over.pullback x).obj A] := by
    rw [MonObj.comp_pow, Category.comp_id, hz', Hom.one_def]
  let g := hK.lift z' (toUnit Z') hcond
  have hgz : g ≫ Sigma.desc (fun c => c.1) = z' := hK.lift_fst _ _ _
  let P := {c : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback x).obj A // c ^ n = 1}
  let D : (∐ fun _ : P => 𝟙_ (Over (Sp k))) ⟶ GlobalTheory.PointQuot.constObj (Sp k) P :=
    Sigma.desc fun c => GlobalTheory.PointQuot.constPt (Sp k) c
  have hDE : D ≫ GlobalTheory.PointQuot.constDesc (fun c : P => c.1) = Sigma.desc (fun c : P => c.1) :=
    Sigma.hom_ext _ _ fun c => by
      rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, GlobalTheory.PointQuot.constPt_desc]
  obtain ⟨U, hwU, c, hc⟩ := GlobalTheory.PointQuot.locally_const_desc (fun c : P => c.1) (g ≫ D) w
  have hU : GlobalTheory.PointQuot.openι Z' U ≫ z' = toUnit _ ≫ c.1 := by
    rw [← hc, ← hgz, ← hDE]
    simp only [Category.assoc]
  let y : Over.mk x ⟶ A := Over.homMk (c.1.left ≫ pullback.fst A.hom x) (by
    show (c.1.left ≫ pullback.fst A.hom x) ≫ A.hom = x
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hc1 : c.1.left ≫ pullback.snd A.hom x = 𝟙 _ := Over.w c.1
    rw [hc1, Category.id_comp])
  let e'' : Over.mk x ⟶ Over.mk ((𝟙_ (Over (Sp k))).hom ≫ x) := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ 𝟙 _ ≫ x = x
    rw [Category.id_comp, Category.id_comp])
  have hy : y = e'' ≫ pushHom hg _ c.1 := Over.OverMorphism.ext (by
    show c.1.left ≫ pullback.fst A.hom x = 𝟙 _ ≫ (c.1.left ≫ pullback.fst A.hom x)
    rw [Category.id_comp])
  refine ⟨GlobalTheory.PointQuot.openObj Z U, GlobalTheory.PointQuot.openι Z U, y, ⟨w, hwU⟩, ?_, rfl, ?_, ?_⟩
  · show IsOpenImmersion U.ι
    infer_instance
  · rw [hy, ← MonObj.comp_pow, ← map_pow, c.2, map_one, MonObj.comp_one]
  · apply Over.OverMorphism.ext
    have h1 := congrArg CommaMorphism.left hU
    have h2 : (toUnit (GlobalTheory.PointQuot.openObj Z' U)).left = U.ι ≫ t.left :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (GlobalTheory.PointQuot.openObj Z' U)))
    show U.ι ≫ z.left = U.ι ≫ t.left ≫ c.1.left ≫ pullback.fst A.hom x
    have h3 : z.left = z'.left ≫ pullback.fst A.hom x := (pullback.lift_fst _ _ _).symm
    simp only [Over.comp_left] at h1
    rw [h3, ← Category.assoc]
    erw [h1, h2]
    exact Category.assoc _ _ _

end GlobalTheory.TorsLocConst
