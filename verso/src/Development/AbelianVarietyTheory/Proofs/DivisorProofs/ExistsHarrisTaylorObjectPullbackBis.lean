import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (by show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left rw [Category.assoc, hab, Category.assoc])`.
-/
theorem push_comp (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A} (hab : α.left ≫ φ = φ ≫ β.left)
    (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

/- English proof (translation)
Take `⟨e₀, he₀⟩` from `GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl`. Establish `one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ`. Rewrite using `[← he₀, map_one]`. Establish `sc : spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R'))`. Use `(Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)` and prove the remaining obligations.

Apply the tactic sequence `ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Establish `fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _`. Use `(Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))` and prove the remaining obligations. Use extensionality with `a`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.

Establish `hR : ∀ (u w : epsPtR x ⟶ A'), u.left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ w.left ↔ (e u).left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ (e w).left` using `fun u w => by`. Rewrite using `[he, he]`. Use `⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩` and prove the remaining obligations. Use `(Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))` and prove the remaining obligations. Use `(congrArg (spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ ·) (Over.w w)).trans ?_` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)`. Use `and_congr ?_ ?_` and prove the remaining obligations. Rewrite using `[one, he]`. Use `⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm, fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩` and prove the remaining obligations. Use `((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm` and prove the remaining obligations.

Use `(congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))`. Establish `E : e (v ≫ a'.act b) = e v ≫ a.act b` using `Over.OverMorphism.ext (by`. Rewrite using `[he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])`. Establish `H` using `hR (v ≫ a'.act b) v`.

Rewrite `H` using `[E]`. Conclude with `H`.
-/
theorem isTanScal_iff (h : IsGrpPullback A' A f φ) {O : Type} [Ring O] (a : OActN O A) (a' : OActN O A')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ A') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A'), u.left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ w.left ↔
      (e u).left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ (e w).left := fun u w => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    have H := hR (v ≫ a'.act b) v
    rw [E] at H
    exact H

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

/- English proof (translation)
Take `⟨u, hu⟩` from `H`. Take `⟨t, ht⟩` from `hx`. Use `GlobalTheory.SiegelPull.push_injective h T ((map_pow _ _ _).trans ((hn _ (pushHom h T x) ?_).trans (map_one _).symm))` and prove the remaining obligations. Set `T₀ : Over S` to `Over.mk (T.hom ≫ f)`. Establish `w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f` using `pullback.condition.trans (Category.assoc _ _ _).symm`.

Set `a : (A ⊗ T₀).left ⟶ A'.left` to `h.1.lift _ _ w₁`. Establish `a₁ : a ≫ φ = (fst A T₀).left` using `h.1.lift_fst _ _ _`. Establish `a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom` using `h.1.lift_snd _ _ _`. Set `χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left` to `pullback.lift a (snd A T₀).left a₂`. Establish `c₁ : χ ≫ (fst A' T).left = a` using `pullback.lift_fst _ _ _`.

Establish `c₂ : χ ≫ (snd A' T).left = (snd A T₀).left` using `pullback.lift_snd _ _ _`. Take `⟨t₂, ht₂, -⟩` from `exists_up ((isGen_iff u).1 hu) hP hP' t ht`. Use `gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂` and prove the remaining obligations. Use `((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]`.

Both sides reduce to the same expression. Rewrite using `[← Category.assoc, c₁, a₁, Category.id_comp]`.
-/
theorem kernel_pullback (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (e : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ e = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine GlobalTheory.SiegelPull.push_injective h T ((map_pow _ _ _).trans ((hn _ (pushHom h T x) ?_).trans (map_one _).symm))
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

/- English proof (translation)
Introduce `p _ D R _ b N S S' s f o`. Set `A'` to `(Over.pullback f).obj o.A`. Set `φ` to `PullbackComparison.pφ f o.A`. Set `φ₂` to `PullbackComparison.pφ₂ f o.A`. Establish `pb : IsGrpPullback A' o.A f φ` using `PullbackComparison.isGrpPullback f o.A`.

Establish `sq : IsSquare φ φ₂` using `PullbackComparison.isSquare f o.A`. Establish `hab : IsAbelianScheme A'` using `{ comm := by have := o.ab.comm; infer_instance smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance geomConnected := by`. Use `o.ab.geomConnected` as an intermediate fact. Use `show GeometricallyConnected (Limits.pullback.snd _ _)`. Use `infer_instance }`.

Take `⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩` from `ActPull.exists_act_pull S S' f o.A A' φ pb D.Oᵐᵒᵖ (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one) (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)`. Set `actN : OActN D.O A'` to `{ act := fun c => act' (MulOpposite.op c) hom := fun c => hhom _ one := by simpa using hone mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _ add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }`. Establish `hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left` using `fun c => hact' (MulOpposite.op c)`. Set `P' : LB (G2 A').left` to `o.P.pull φ₂`. Establish `hP' : P'.IsLB` using `pull_isLB o.isLB φ₂`.

Establish `iso : LBIso P' (o.P.pull φ₂)` using `PullbackComparison.gen_refl _ hP'`. Establish `dg` using `SiegelPull.diag_iso sq iso`. Establish `sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left → (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left` using `fun x' y' x y hx hy => (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y' (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))`. Take `⟨t₁, ht₁⟩` from `o.rig₁`. Take `⟨t₂, ht₂⟩` from `o.rig₂`.

Take `⟨eK, heK, hK⟩` from `o.kerP`. Set `o' : Obj b N (f ≫ s)` to `{ A := A' ab := hab act := actN P := P' isLB := hP' rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁ rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂`. Use symmetry as in `:= LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl) (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm`. Use `ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample`. Use `kerP := ⟨eK, heK, fun T x hx => kernel_pullback pb sq o.isLB hP' iso eK hK T x hx⟩`.

Use `rosati := fun c => LBIso.chartPull (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])`. Use the proof step `(by rw [sq.2])))`. Use the proof step `(chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))`.

Use the proof step `(o.rosati c)`. Use `lie := fun R' _ β x hx v hv => by`. Take `⟨e, he⟩` from `GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f) (Category.assoc _ _ _).symm`. Take `⟨w, hw, hvw⟩` from `o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v) ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)`. Use `⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2 (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[hvw, map_list_prod, List.map_ofFn]`. Simplify using `[Function.comp_def]`. Use `lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A A' f φ (o.act.toF D) (actN.toF D) pb (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)`. Use `eta := fun y => SiegelPull.secPull pb (o.eta y)`. Use `eta_add := fun y z => SiegelPull.push_injective pb _ (by`.

Rewrite using `[map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])`. Use `eta_lin := fun c y => SiegelPull.push_injective pb _ (by`. Rewrite using `[push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])`. Use `eta_ker := fun y => SiegelPull.push_injective pb _ (by`. Rewrite using `[push_secPull', o.eta_ker, map_one, MonObj.comp_one])`.

Use `geom := fun k _ _ x β hx => by`. Take `⟨I, hI⟩` from `o.geom k (x ≫ f) β (by rw [Category.assoc, hx])`. Set `e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A)` to `MulEquiv.ofBijective (pushHom pb (Over.mk x)) ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩`. Establish `ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c` using `fun c g => push_comp pb (hact c) _ g`. Establish `ex : ∀ z, z.left = (e.symm z).left ≫ φ` using `fun z => (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm`.

Use `⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y) add := fun n y z => by rw [I.add, map_mul] lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin]) ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.inje …` and prove the remaining obligations. Rewrite using `[← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]`. Conclude with `exists_congr fun y => e.symm_apply_eq.symm`. Use `tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]`. Use `isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩`.

Use `show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)`. Rewrite using `[eq_comm, e.symm_apply_eq, ← hI y]`. Conclude with `(SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }`. Conclude with `⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩`.
-/
theorem exists_objMap_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb D.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  obtain ⟨eK, heK, hK⟩ := o.kerP
  let o' : Obj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      kerP := ⟨eK, heK, fun T x hx => kernel_pullback pb sq o.isLB hP' iso eK hK T x hx⟩
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A A' f φ (o.act.toF D) (actN.toF D) pb
        (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end GlobalTheory.HTPull
