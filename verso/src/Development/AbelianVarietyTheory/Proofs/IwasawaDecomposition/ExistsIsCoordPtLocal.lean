import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistEqResc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsArcFamilyPointWithFramesProof
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPointsCoordsRelabelledTwistedDataSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsCoordPtFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM.MultiPt
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.CoordReduce

open ReciprocityTheory.ChartRestriction.G.Out in

/- English proof (translation)
Establish `hG` using `h₁.globalFns`. Establish `hL` using `P.isLB`. Establish `cg` using `GlobalTheory.AbLaw.CubeAssembly.cube_gen`. Establish `neg` using `GlobalTheory.exists_gen_negLB hG`. Establish `sym` using `(GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1`.

Take `⟨V, hV, b, hb⟩` from `h₂.secBaseChangeAny B P 1 le_rfl (s (IsLocalRing.closedPoint R))`. Take `⟨t, rfl⟩ : ∃ t : Sp R ⟶ (overRes (T` from `baseOver B) V).left, t ≫ (overRes (T := baseOver B) V).hom = s := ⟨IsOpenImmersion.lift V.ι s (by`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `(IsLocalRing.specializes_closedPoint (R := R) p).mem_open (s ⁻¹ᵁ V).isOpen hV),`.

Use the proof step `(congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩`. Take `⟨-, hsp⟩` from `hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _`. Use `haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance`. Take `⟨th₀, hth₀⟩` from `ThetaLocal.exists_generator _ hsp`. Set `T : Over B` to `baseAt t`.

Take `⟨th, hth⟩` from `ThetaPtExist.exists_isGenSec_of_retract hL (𝟙 T) (𝟙 T) (Category.comp_id _) th₀ hth₀`. Take `⟨α₀, hα₀⟩` from `h₁.mulPull B P k`. Take `⟨α, hα, -⟩` from `VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) α₀ hα₀ (snd T P.A).left (fun i => by fin_cases i`. Conclude with `Category.comp_id _`. Express the relevant statement in the definitionally equal form `(snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left`.

Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id])`. Take `⟨s₁, hs₁⟩` from `ThetaPtExist.exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th`. Establish `hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ` using `fun i => by`. Take `⟨U, hU, θ, hθ⟩` from `(sym B P (k ^ 2) hk.pow T (x i) (hx i)).1 (IsLocalRing.closedPoint R)`. Take `rfl : U = ⊤` from `(IsLocalRing.closedPoint_mem_iff U).1 hU`.

Set `h : T ⟶ overRes (T` to `T) ⊤ := Over.homMk (Sp R).topIso.inv (by show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ _ = _`. Rewrite using `[Scheme.toIso_inv_ι_assoc])`. Establish `hh : h ≫ overResι ⊤ = 𝟙 _` using `Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))`. Take `⟨θ', hθ'⟩` from `GlobalLift.exists_symLift_pull P.isLB h hθ`. Rewrite `hθ'` using `[← Category.assoc, hh, Category.id_comp]`.

Rewrite using `[← Nat.cast_pow]`. Conclude with `⟨θ', hθ'⟩`. Use `choose U hU using hU`. Use `choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _) ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁`. Take `⟨c, hc⟩` from `Geo.Tor.exists_chart hL (z.left (IsLocalRing.closedPoint R))`.

Take `⟨τ, hτ⟩` from `AbSquare.exists_gen_of_mem_chart hL (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => (k : ℤ) ^ 2) (fun _ => c) fun _ y => ((IsLocalRing.specializes_closedPoint (R := R) y).map z.left.continuous).mem_open (P.L.U c).isOpen hc`. Use `choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) z τ hτ`. Use `⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (w i), hk, ?_, th, s₁, α, τ, U, s₂, hth, hα, hτ, hs₁, hU, hs₂, fun i => ?_⟩` and prove the remaining obligations. Use `hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Use `hw i using 1` and compare the differences between its conclusion and the goal. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (w i)`.
-/
theorem exists_isCoordPt_local (h₁ : Laws) (h₂ : Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : R)) {J : Type}
    (x : J → (Over.mk s ⟶ P.A)) (hx : ∀ i, x i ^ k ^ 2 = 1) (z : Over.mk s ⟶ P.A) :
    ∃ w : J → R, IsCoordPt P k x z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i) := by
  have hG := h₁.globalFns
  have hL := P.isLB
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V, hV, b, hb⟩ := h₂.secBaseChangeAny B P 1 le_rfl (s (IsLocalRing.closedPoint R))
  obtain ⟨t, rfl⟩ : ∃ t : Sp R ⟶ (overRes (T := baseOver B) V).left, t ≫ (overRes (T := baseOver B) V).hom = s :=
    ⟨IsOpenImmersion.lift V.ι s (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open (s ⁻¹ᵁ V).isOpen hV),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th₀, hth₀⟩ := ThetaLocal.exists_generator _ hsp
  let T : Over B := baseAt t
  obtain ⟨th, hth⟩ := ThetaPtExist.exists_isGenSec_of_retract hL (𝟙 T) (𝟙 T) (Category.comp_id _) th₀ hth₀
  obtain ⟨α₀, hα₀⟩ := h₁.mulPull B P k
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) α₀ hα₀
    (snd T P.A).left (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _)
    ((k : ℤ) ^ 2) 1 α hα th
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ := fun i => by
    obtain ⟨U, hU, θ, hθ⟩ := (sym B P (k ^ 2) hk.pow T (x i) (hx i)).1 (IsLocalRing.closedPoint R)
    obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
    let h : T ⟶ overRes (T := T) ⊤ := Over.homMk (Sp R).topIso.inv (by
      show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ _ = _
      rw [Scheme.toIso_inv_ι_assoc])
    have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB h hθ
    rw [← Category.assoc, hh, Category.id_comp] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt)
    (lift_snd _ _) ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  obtain ⟨c, hc⟩ := Geo.Tor.exists_chart hL (z.left (IsLocalRing.closedPoint R))
  obtain ⟨τ, hτ⟩ := AbSquare.exists_gen_of_mem_chart hL (Y := T.left) (K := Fin 1) (fun _ => z.left)
    (fun _ => (k : ℤ) ^ 2) (fun _ => c) fun _ y =>
      ((IsLocalRing.specializes_closedPoint (R := R) y).map z.left.continuous).mem_open (P.L.U c).isOpen hc
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) z τ hτ
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (w i), hk, ?_, th, s₁, α, τ, U, s₂, hth, hα, hτ, hs₁,
    hU, hs₂, fun i => ?_⟩
  · have := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  · convert hw i using 1
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (w i)

open ReciprocityTheory.ChartRestriction.G.Out in

/- English proof (translation)
Establish `: IsAffine (Over.mk s).left` using `inferInstanceAs (IsAffine (Spec _))`. Establish `: IsAffine (Over.mk x).left` using `inferInstanceAs (IsAffine (Spec _))`. Set `jx : Over.mk x ⟶ Over.mk s` to `Over.homMk (spMap j) hx`. Establish `Q` using `FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx (Category.id_comp _) (hx.trans (Category.comp_id _).symm) (fun th₀ h => EmbPull.isGenSec_pullS P …`. Use `Q using 2 with a` and compare the differences between its conclusion and the goal.

Conclude with `congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))`.
-/
theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

/- English proof (translation)
Introduce `h₁ h₂ B _ P C κ _ _ _ _ S res s x y hx hy m hm hu J p hp ho z v H hv`. Establish `hk : Odd m` using `H.1`. Take `⟨w, hw⟩` from `exists_isCoordPt_local h₁ h₂ P s hk hu p hp z`. Establish `hC` using `isCoordPt_map h₂ P S.subtype hx hp hw`. Establish `hK` using `isCoordPt_map h₂ P res hy hp hw`.

Establish `hmC : (m : C) ≠ 0`. Use `hu.map S.subtype` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this.ne_zero`. Establish `hmκ : (m : κ) ≠ 0`.

Use `hu.map res` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this.ne_zero`. Establish `pw : ∀ {K : Type} [CommRing K] (j : S →+* K) {x' : Sp K ⟶ B} (hx' : spMap j ≫ s = x') (i : J), ((Over.homMk (spMap j) hx' : Over.mk x' ⟶ Over.mk s) ≫ p i) ^ m ^ 2 = 1`. Introduce `K _ j x' hx' i`.

Rewrite using `[← MonObj.comp_pow, hp i, MonObj.comp_one]`. Take `⟨-, U₂, -, -⟩` from `CoordSep.coord_exists_unique_separate h₁ C B P x m hk hmC J _ (pw S.subtype hx)`. Take `⟨c, hc⟩` from `(U₂ _ (fun i => (w i : C)) (fun i => (v i : C)) hC).1 H`. Take `⟨-, -, -, U₄⟩` from `CoordSep.coord_exists_unique_separate h₁ κ B P y m hk hmκ J _ (pw res hy)`. Take `⟨i, hi⟩` from `Function.ne_iff.1 (U₄ hm ho _ _ (fun i => res (w i)) hK hK).2`.

Take `⟨d, hd, hd'⟩` from `Specialise.exists_res_eq_mul S res (c := c) (fun i => congrFun hc i) hv ⟨i, hi⟩`. Use `RelabelCoords.isCoordPt_unit_mul ((IsUnit.mk0 d hd).map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom).unit (fun i => ?_) hK` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, hd' i]`. Conclude with `map_mul _ _ _`.
-/
theorem isCoordPt_reduce : ∀ (h₁ : Out.Laws) (h₂ : Out.Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : Out.PolAV B)
    {C κ : Type} [Field C] [IsAlgClosed C] [Field κ] [IsAlgClosed κ] (S : ValuationSubring C) (res : S →+* κ)
    {s : Sp S ⟶ B} {x : Sp C ⟶ B} {y : Sp κ ⟶ B} (hx : spMap S.subtype ≫ s = x) (hy : spMap res ≫ s = y)
    {m : ℕ}, 3 ≤ m → IsUnit (m : S) → ∀ {J : Type} (p : J → (Over.mk s ⟶ P.A)), (∀ i, p i ^ m ^ 2 = 1) →
    (∀ z : Over.mk y ⟶ P.A, z ^ m ^ 2 = 1 →
      ∃ i, (Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ p i = z) →
    ∀ (z : Over.mk s ⟶ P.A) (v : J → S),
    IsCoordPt P m (fun i => (Over.homMk (spMap S.subtype) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap S.subtype) hx : Over.mk x ⟶ Over.mk s) ≫ z) (fun i => fnOf (v i : C)) →
    (∃ i, res (v i) ≠ 0) →
    IsCoordPt P m (fun i => (Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap res) hy : Over.mk y ⟶ Over.mk s) ≫ z) fun i => fnOf (res (v i)) := by
  intro h₁ h₂ B _ P C κ _ _ _ _ S res s x y hx hy m hm hu J p hp ho z v H hv
  have hk : Odd m := H.1
  obtain ⟨w, hw⟩ := exists_isCoordPt_local h₁ h₂ P s hk hu p hp z
  have hC := isCoordPt_map h₂ P S.subtype hx hp hw
  have hK := isCoordPt_map h₂ P res hy hp hw
  have hmC : (m : C) ≠ 0 := by
    have := hu.map S.subtype
    rw [map_natCast] at this
    exact this.ne_zero
  have hmκ : (m : κ) ≠ 0 := by
    have := hu.map res
    rw [map_natCast] at this
    exact this.ne_zero
  have pw : ∀ {K : Type} [CommRing K] (j : S →+* K) {x' : Sp K ⟶ B} (hx' : spMap j ≫ s = x') (i : J),
      ((Over.homMk (spMap j) hx' : Over.mk x' ⟶ Over.mk s) ≫ p i) ^ m ^ 2 = 1 := by
    intro K _ j x' hx' i
    rw [← MonObj.comp_pow, hp i, MonObj.comp_one]
  obtain ⟨-, U₂, -, -⟩ := CoordSep.coord_exists_unique_separate h₁ C B P x m hk hmC J _ (pw S.subtype hx)
  obtain ⟨c, hc⟩ := (U₂ _ (fun i => (w i : C)) (fun i => (v i : C)) hC).1 H
  obtain ⟨-, -, -, U₄⟩ := CoordSep.coord_exists_unique_separate h₁ κ B P y m hk hmκ J _ (pw res hy)
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (U₄ hm ho _ _ (fun i => res (w i)) hK hK).2
  obtain ⟨d, hd, hd'⟩ := Specialise.exists_res_eq_mul S res (c := c) (fun i => congrFun hc i) hv ⟨i, hi⟩
  refine RelabelCoords.isCoordPt_unit_mul ((IsUnit.mk0 d hd).map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom).unit
    (fun i => ?_) hK
  rw [IsUnit.unit_spec, hd' i]
  exact map_mul _ _ _

end GlobalTheory.CoordReduce
