import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HTLift

open GlobalTheory.SiegelPull

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (by show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left rw [Category.assoc, hab, Category.assoc])`.
-/
theorem push_comp' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A}
    (hab : α.left ≫ φ = φ ≫ β.left) (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

/- English proof (translation)
Introduce `p _ D R _ b N N' hd hc S s o T lv hL`. Take `⟨hadd, hker, hlin, hlev, hgeom⟩` from `hL`. Take `⟨oT, ⟨mT⟩⟩` from `GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S T.left s T.hom o`. Establish `pb` using `mT.cart`. Set `eta : D.La → (𝟙_ (Over T.left) ⟶ oT.A)` to `fun a => Over.homMk (pb.1.lift (lv a).left (𝟙 _) (by rw [Over.w, Category.id_comp])) (pb.1.lift_snd _ _ _)`.

Establish `etaφ : ∀ a, (eta a).left ≫ mT.φ = (lv a).left` using `fun a => pb.1.lift_fst _ _ _`. Set `u : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`. Establish `key : ∀ a, pushHom pb _ (eta a) = u ≫ lv a` using `fun a => Over.OverMorphism.ext (by show (eta a).left ≫ mT.φ = 𝟙 T.left ≫ (lv a).left`. Rewrite using `[Category.id_comp]`. Conclude with `etaφ a)`.

Set `o'' : Obj b N' (T.hom ≫ s)` to `{ A := oT.A ab := oT.ab act := oT.act P := oT.P isLB := oT.isLB rig₁ := oT.rig₁ rig₂ := oT.rig₂`. Use symmetry as in `:= oT.symm`. Use `ample := oT.ample`. Use `kerP := oT.kerP`. Use `rosati := oT.rosati`.

Use `lie := oT.lie`. Use `lieRank := oT.lieRank`. Use `eta := eta`. Use `eta_add := fun y z => push_injective pb _ (by`. Rewrite using `[map_mul, key, key, key, hadd, MonObj.comp_mul])`.

Use `eta_lin := fun c y => push_injective pb _ (by`. Rewrite using `[push_comp' pb (mT.act c), key, key, hlin, Category.assoc])`. Use `eta_ker := fun y => push_injective pb _ (by`. Rewrite using `[key, hker, map_one, MonObj.comp_one])`. Use `geom := fun k _ _ x β hx => by`.

Take `⟨I, hI⟩` from `hgeom k x`. Set `e : (Over.mk x ⟶ oT.A) ≃* (Over.mk (x ≫ T.hom) ⟶ o.A)` to `MulEquiv.ofBijective (pushHom pb (Over.mk x)) ⟨push_injective pb _, push_surjective pb _⟩`. Establish `ea : ∀ c g, e (g ≫ oT.act.act c) = e g ≫ o.act.act c` using `fun c g => push_comp' pb (mT.act c) _ g`. Establish `ex : ∀ z, z.left = (e.symm z).left ≫ mT.φ` using `fun z => (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm`. Establish `dg` using `diag_iso mT.sq mT.pol`.

Use `⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y) add := fun n y z => by rw [I.add, map_mul] lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin]) ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.inje …` and prove the remaining obligations. Rewrite using `[← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]`. Conclude with `exists_congr fun y => e.symm_apply_eq.symm`. Use `tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]`. Use `isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S T.left o.A oT.A T.hom mT.φ _ _ (pull_isLB o.isLB _) (pull_isLB oT.isLB _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩`.

Use `show toUnit _ ≫ eta y = e.symm (I.ev N' y)`. Rewrite using `[eq_comm, e.symm_apply_eq, ← hI y]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show x ≫ (lv y).left = ((toUnit (Over.mk x)).left ≫ (eta y).left) ≫ mT.φ`. Rewrite using `[Category.assoc, etaφ, Over.toUnit_left]`.

Use `rfl }`. Set `mm : ObjMap (o''.forget N hd hc) o T.hom` to `{ φ := mT.φ, φ₂ := mT.φ₂, cart := mT.cart, sq := mT.sq, act := mT.act, pol := mT.pol, eta := fun y => by show (eta ((N' / N) • y)).left ≫ mT.φ = T.hom ≫ (o.eta y).left`. Rewrite using `[etaφ, hlev, Over.comp_left, Over.toUnit_left] }`. Conclude with `⟨o'', mm, fun a => etaφ a⟩`.
-/
theorem exists_obj_of_isLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S)
    (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s))
    (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  intro p _ D R _ b N N' hd hc S s o T lv hL
  obtain ⟨hadd, hker, hlin, hlev, hgeom⟩ := hL
  obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S T.left s T.hom o
  have pb := mT.cart
  let eta : D.La → (𝟙_ (Over T.left) ⟶ oT.A) := fun a =>
    Over.homMk (pb.1.lift (lv a).left (𝟙 _) (by rw [Over.w, Category.id_comp])) (pb.1.lift_snd _ _ _)
  have etaφ : ∀ a, (eta a).left ≫ mT.φ = (lv a).left := fun a => pb.1.lift_fst _ _ _
  let u : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, pushHom pb _ (eta a) = u ≫ lv a := fun a => Over.OverMorphism.ext (by
    show (eta a).left ≫ mT.φ = 𝟙 T.left ≫ (lv a).left
    rw [Category.id_comp]; exact etaφ a)
  let o'' : Obj b N' (T.hom ≫ s) :=
    { A := oT.A
      ab := oT.ab
      act := oT.act
      P := oT.P
      isLB := oT.isLB
      rig₁ := oT.rig₁
      rig₂ := oT.rig₂
      symm := oT.symm
      ample := oT.ample
      kerP := oT.kerP
      rosati := oT.rosati
      lie := oT.lie
      lieRank := oT.lieRank
      eta := eta
      eta_add := fun y z => push_injective pb _ (by
        rw [map_mul, key, key, key, hadd, MonObj.comp_mul])
      eta_lin := fun c y => push_injective pb _ (by
        rw [push_comp' pb (mT.act c), key, key, hlin, Category.assoc])
      eta_ker := fun y => push_injective pb _ (by
        rw [key, hker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := hgeom k x
        let e : (Over.mk x ⟶ oT.A) ≃* (Over.mk (x ≫ T.hom) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨push_injective pb _, push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ oT.act.act c) = e g ≫ o.act.act c := fun c g => push_comp' pb (mT.act c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ mT.φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        have dg := diag_iso mT.sq mT.pol
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S T.left o.A oT.A T.hom mT.φ _ _
                    (pull_isLB o.isLB _) (pull_isLB oT.isLB _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _
                    (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ eta y = e.symm (I.ev N' y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        apply Over.OverMorphism.ext
        show x ≫ (lv y).left = ((toUnit (Over.mk x)).left ≫ (eta y).left) ≫ mT.φ
        rw [Category.assoc, etaφ, Over.toUnit_left]
        rfl }
  let mm : ObjMap (o''.forget N hd hc) o T.hom :=
    { φ := mT.φ, φ₂ := mT.φ₂, cart := mT.cart, sq := mT.sq, act := mT.act, pol := mT.pol,
      eta := fun y => by
        show (eta ((N' / N) • y)).left ≫ mT.φ = T.hom ≫ (o.eta y).left
        rw [etaφ, hlev, Over.comp_left, Over.toUnit_left] }
  exact ⟨o'', mm, fun a => etaφ a⟩

end GlobalTheory.HTLift
