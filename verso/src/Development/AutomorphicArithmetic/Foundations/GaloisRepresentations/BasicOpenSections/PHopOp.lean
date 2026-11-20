import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.HopfOperations

/- English proof (translation)
Use `(h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)` as an intermediate fact. Simplify using `using this`.
-/
private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

/- English proof (translation)
Establish `h` using `TranscendenceTraces.multBasic_holds.2.2 p`. Rewrite using `[← h]`. Conclude with `TranscendenceTraces.wtFlat_holds p`.
-/
private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : TranscendenceTraces.IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @IsFinite) h ‹_›`.
-/
private theorem fin_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [IsFinite p] : IsFinite s :=
  MorphismProperty.of_isPullback (P := @IsFinite) h ‹_›

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @Etale) h ‹_›`.
-/
private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

/- English proof (translation)
Unfold `pullHQ`. Rewrite using `[pullHl_comp]`. Conclude with `LinearMap.baseChange_comp _ _`.
-/
private theorem pullQ_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
private theorem gm_fst {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
private theorem gm_snd {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

/- English proof (translation)
Use `IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_ (gm_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)` and prove the remaining obligations. Rewrite using `[gm_snd]`. Conclude with `IsPullback.of_hasPullback _ _`.
-/
private theorem gm_pb {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (gm_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [gm_snd]
  exact IsPullback.of_hasPullback _ _

/- English proof (translation)
The claim follows from `Nat.card_congr { toFun := fun y => ⟨y.1 ≫ a, by rw [Category.assoc, h.w, reassoc_of% y.2]⟩ invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩ left_inv := fun y => Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (by rw [h.lift_snd, y.2])) right_inv := fun y => Subtype.ext (h.lift_f …`.
-/
private theorem card_pb {A B C D P : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) (x : P ⟶ B) :
    Nat.card {y : P ⟶ A // y ≫ v = x} = Nat.card {y : P ⟶ C // y ≫ u = x ≫ b} :=
  Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ a, by rw [Category.assoc, h.w, reassoc_of% y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y => Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (by rw [h.lift_snd, y.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }

end UpperTheory.Gal.Mod.HopfOperations

open UpperTheory.Gal.Mod.HopfOperations in
/- English proof (translation)
Introduce `hGal hOp l _ k _ H Ω _ _ hlΩ g d hd`. Take `⟨hF, hE, hcard⟩` from `hd`. Use `haveI := hF`. Use `haveI := hE`. Establish `hpb : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) (H.sΩ Ω g) (H.s g) (pullback.fst H.q (sp (algebraMap k Ω)))` using `gm_pb Ω H.q (H.s g)`.

Use `haveI hsF : IsFinite (H.sΩ Ω g) := fin_of_pb hpb`. Use `haveI hsE : Etale (H.sΩ Ω g) := et_of_pb hpb`. Establish `hFEt : FEt (H.sΩ Ω g) d` using `⟨hsF, hsE, fun K _ _ x => (card_pb hpb x).trans (hcard K _)⟩`. Establish `hlZ : IsUnit (l : Γ(H.geomZ Ω, ⊤))` using `isUnit_nat (pullback.snd H.q (sp (algebraMap k Ω))) l hlΩ.ne_zero`. Take `⟨W, c, G, iG, fG, a, σ, hG, hs⟩` from `hGal (H.sΩ Ω g) d hFEt`.

Take `⟨hσ, hiso⟩` from `id hs`. Establish `hsplit` using `fun n : ℤ => TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l n 0 (H.sΩ Ω g) hlZ W c d σ hσ hiso`. Set `T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω))` to `DirectSum.lmap fun n : ℤ => trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 ∘ₗ pullHQ l (sch.map (H.tΩ Ω g)) n 0`. Establish `hcomp : pullTot l (sch.map c) ∘ₗ T = ∑ j, pullTot l (sch.map (σ j ≫ H.tΩ Ω g))`. Use `DirectSum.linearMap_ext _ fun n => LinearMap.ext fun y => ?_` and prove the remaining obligations.

Establish `h1` using `LinearMap.congr_fun (hsplit n) (pullHQ l (sch.map (H.tΩ Ω g)) n 0 y)`. Simplify using `only [LinearMap.comp_apply, LinearMap.sum_apply] at h1 ⊢`. Simplify using `only [T, pullTot, DirectSum.lmap_lof, LinearMap.comp_apply, h1, map_sum, Functor.map_comp, pullQ_comp, LinearMap.sum_apply]`. Establish `hT : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T` using `⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hG, hs, fun x => by`. Rewrite using `[← LinearMap.sum_apply, ← hcomp]`.

Use the proof step `rfl⟩`. Set `cc : TranscendenceTraces.Corr (H.geomZ Ω) (H.geomZ Ω)` to `⟨_, H.sΩ Ω g, H.tΩ Ω g, Wt.const _ 1, inferInstance, isWt_one _⟩`. Use `haveI : Etale cc.p := hsE`. Establish `hex : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T` using `⟨T, hT⟩`. Establish `e1` using `hOp l cc rfl hlZ T hT`.

Establish `e2` using `hOp l cc rfl hlZ _ hex.choose_spec`. Establish `hh : hop l H Ω g = hex.choose` using `by unfold hop; rw [dif_pos hex]`. Rewrite using `[hh, e2]`. Conclude with `e1.symm`.
-/
theorem UpperTheory.Gal.Mod.hopOp :
    GalEx → CorrOpEq → HopOp := by
  intro hGal hOp l _ k _ H Ω _ _ hlΩ g d hd
  obtain ⟨hF, hE, hcard⟩ := hd
  haveI := hF
  haveI := hE
  have hpb : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) (H.sΩ Ω g) (H.s g)
      (pullback.fst H.q (sp (algebraMap k Ω))) := gm_pb Ω H.q (H.s g)
  haveI hsF : IsFinite (H.sΩ Ω g) := fin_of_pb hpb
  haveI hsE : Etale (H.sΩ Ω g) := et_of_pb hpb
  have hFEt : FEt (H.sΩ Ω g) d :=
    ⟨hsF, hsE, fun K _ _ x => (card_pb hpb x).trans (hcard K _)⟩
  have hlZ : IsUnit (l : Γ(H.geomZ Ω, ⊤)) :=
    isUnit_nat (pullback.snd H.q (sp (algebraMap k Ω))) l hlΩ.ne_zero
  obtain ⟨W, c, G, iG, fG, a, σ, hG, hs⟩ := hGal (H.sΩ Ω g) d hFEt
  obtain ⟨hσ, hiso⟩ := id hs
  have hsplit := fun n : ℤ => TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l n 0 (H.sΩ Ω g) hlZ W c d σ hσ hiso
  let T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    DirectSum.lmap fun n : ℤ => trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 ∘ₗ pullHQ l (sch.map (H.tΩ Ω g)) n 0
  have hcomp : pullTot l (sch.map c) ∘ₗ T = ∑ j, pullTot l (sch.map (σ j ≫ H.tΩ Ω g)) := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun y => ?_
    have h1 := LinearMap.congr_fun (hsplit n) (pullHQ l (sch.map (H.tΩ Ω g)) n 0 y)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1 ⊢
    simp only [T, pullTot, DirectSum.lmap_lof, LinearMap.comp_apply, h1, map_sum, Functor.map_comp, pullQ_comp,
      LinearMap.sum_apply]
  have hT : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T :=
    ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hG, hs, fun x => by
      rw [← LinearMap.sum_apply, ← hcomp]; rfl⟩
  let cc : TranscendenceTraces.Corr (H.geomZ Ω) (H.geomZ Ω) :=
    ⟨_, H.sΩ Ω g, H.tΩ Ω g, Wt.const _ 1, inferInstance, isWt_one _⟩
  haveI : Etale cc.p := hsE
  have hex : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T := ⟨T, hT⟩
  have e1 := hOp l cc rfl hlZ T hT
  have e2 := hOp l cc rfl hlZ _ hex.choose_spec
  have hh : hop l H Ω g = hex.choose := by unfold hop; rw [dif_pos hex]
  rw [hh, e2]
  exact e1.symm
