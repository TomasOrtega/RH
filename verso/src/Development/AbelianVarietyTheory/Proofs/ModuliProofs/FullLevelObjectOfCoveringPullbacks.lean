import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

/- English proof (translation)
Take `⟨q, hq⟩` from `hp`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm`. Set `Ω : Type` to `AlgebraicClosure ((pullback x f).residueField z)`. Set `u : Sp Ω ⟶ pullback x f` to `Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z`. Use `⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩` and prove the remaining obligations.

Establish `e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f` using `Spec.map_preimage _`. Rewrite using `[e]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)`.
-/
theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) {k : Type} [Field k] (x : Sp k ⟶ S) (p : Sp k)
    (hp : x p ∈ Set.range f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : k →+* Ω) (y : Sp Ω ⟶ S'), spMap i ≫ x = y ≫ f := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm
  let Ω : Type := AlgebraicClosure ((pullback x f).residueField z)
  let u : Sp Ω ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩
  have e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f := Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

/- English proof (translation)
Substitute `hx` using the available equality. Establish `hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F)`. Take `⟨w, hw, -⟩` from `ν.lin`. Conclude with `⟨w, hw⟩`. Use `⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I, rfl, fun _ _ => rfl⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `(ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g`. Rewrite using `[MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _`. Rewrite using `[Category.assoc, ← ν.act, Category.assoc]`.

Conclude with `(weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc`.
-/
theorem tate_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {k : Type} [Field k] {y : Sp k ⟶ S'} {x : Sp k ⟶ S} (hx : x = y ≫ f)
    (I : TateIso D k (Over.mk y ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
        (fun m g g' c => Out.WeilIs t'.G t'.PP.L m g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      J.ζ = I.ζ ∧ ∀ m a, (J.ev m a).left = (I.ev m a).left ≫ ν.φ := by
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    rfl, fun _ _ => rfl⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc

/- English proof (translation)
Take `⟨P, φ, -, hφ, -⟩` from `exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x`. Take `⟨hinj, honto⟩` from `torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)`. Take `⟨e, he⟩` from `exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm`. Take `⟨e', he'⟩` from `exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)`. Establish `key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) = e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y)` using `fun y => by`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[he']`. Use `show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ`. Rewrite using `[he]`. Conclude with `(Category.assoc _ _ _).symm`.

Use `⟨fun y y' h => ?_, fun m hm z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `e.surjective y`. Take `⟨y', rfl⟩` from `e.surjective y'`. Rewrite `h` using `[key, key]`. Conclude with `congrArg e (hinj (e'.injective h))`.

Take `⟨z, rfl⟩` from `e'.surjective z`. Rewrite `hz` using `[← map_pow, map_eq_one_iff _ e'.injective]`. Take `⟨y, hy, rfl⟩` from `honto m z (Nat.cast_ne_zero.2 hm.ne') hz`. Conclude with `⟨e y, by rw [← map_pow, hy, map_one], key y⟩`.
-/
theorem torsion_ext (hL : Out.Laws) {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) :
    Function.Injective (TateIsoFieldExt.precomp
        (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G) ∧
      ∀ m, 0 < m → ∀ z : Over.mk (spMap i ≫ x) ⟶ t.G, z ^ m = 1 → ∃ y : Over.mk x ⟶ t.G, y ^ m = 1 ∧
        TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G y = z := by
  obtain ⟨P, φ, -, hφ, -⟩ := exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x
  obtain ⟨hinj, honto⟩ := torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)
  have key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) =
      e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y) := fun y => by
    apply Over.OverMorphism.ext
    rw [he']
    show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ
    rw [he]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun y y' h => ?_, fun m hm z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [key, key] at h
    exact congrArg e (hinj (e'.injective h))
  · obtain ⟨z, rfl⟩ := e'.surjective z
    rw [← map_pow, map_eq_one_iff _ e'.injective] at hz
    obtain ⟨y, hy, rfl⟩ := honto m z (Nat.cast_ne_zero.2 hm.ne') hz
    exact ⟨e y, by rw [← map_pow, hy, map_one], key y⟩

/- English proof (translation)
Introduce `hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov`. Use `⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩` and prove the remaining obligations. Take `⟨S', f, t', ν, lv', hq, hl, o⟩` from `hcov (x (default : PrimeSpectrum k))`. Take `⟨Ω, _, _, i, y, hy⟩` from `exists_lift f x _ hq`. Establish `: CharZero Ω` using `(i.charZero_iff i.injective).1 inferInstance`.

Establish `hy' : y ≫ f ≫ s = spMap (i.comp β)`. Rewrite using `[← Category.assoc, ← hy, Category.assoc, hx]`. Conclude with `(Spec.map_comp _ _).symm`. Take `⟨hdet, I', hI', hA'⟩` from `o.geom Ω y (i.comp β) hy'`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `(detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_` and prove the remaining obligations. Rewrite using `[hy]`. Conclude with `(detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet`. Take `⟨J, hJ, hJ'⟩` from `tate_push ν hy I'`. Take `⟨hinj, honto⟩` from `torsion_ext hL t hp ha hk i x`.

Set `g : Over.mk (spMap i ≫ x) ⟶ Over.mk x` to `Over.homMk (spMap i) rfl`. Take `⟨I, hI⟩` from `TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G) (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a) (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto (fun c z => …`. Conclude with `MonObj.one_comp (t.act.act c))`. Use the proof step `(fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J`. Take `⟨h₁, h₂⟩` from `hI N hN`.

Use `⟨I, i.injective ?_, fun a => hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← h₁, hJ, hI']`. Both sides reduce to the same expression. Rewrite using `[← h₂]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]`. Use `show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left`. Rewrite using `[Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]`. Conclude with `(Category.assoc _ _ _).symm`.
-/
theorem fullObj_of_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  intro hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  obtain ⟨S', f, t', ν, lv', hq, hl, o⟩ := hcov (x (default : PrimeSpectrum k))
  obtain ⟨Ω, _, _, i, y, hy⟩ := exists_lift f x _ hq
  have : CharZero Ω := (i.charZero_iff i.injective).1 inferInstance
  have hy' : y ≫ f ≫ s = spMap (i.comp β) := by
    rw [← Category.assoc, ← hy, Category.assoc, hx]
    exact (Spec.map_comp _ _).symm
  obtain ⟨hdet, I', hI', hA'⟩ := o.geom Ω y (i.comp β) hy'
  refine ⟨?_, ?_⟩
  · refine (detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_
    rw [hy]
    exact (detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet
  obtain ⟨J, hJ, hJ'⟩ := tate_push ν hy I'
  obtain ⟨hinj, honto⟩ := torsion_ext hL t hp ha hk i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  obtain ⟨I, hI⟩ := TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G)
    (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a)
    (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c))
    (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto
    (fun c z => (Category.assoc g z (t.act.act c)).symm)
    (fun c => by
      haveI := t.act.hom c
      exact MonObj.one_comp (t.act.act c))
    (fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c
      ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J
  obtain ⟨h₁, h₂⟩ := hI N hN
  refine ⟨I, i.injective ?_, fun a => hinj ?_⟩
  · rw [← h₁, hJ, hI']
    rfl
  · rw [← h₂]
    apply Over.OverMorphism.ext
    rw [hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]
    show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left
    rw [Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.FullDescent
