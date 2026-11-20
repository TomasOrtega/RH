import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BaseChangeExamples

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
The claim follows from `MorphismProperty.of_isPullback (P := @Etale) h ‹_›`.
-/
private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

/- English proof (translation)
Establish `hr : Set.range e ⊆ Set.range (D.basicOpen f).ι`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : x ∈ e ⁻¹ᵁ D.basicOpen f`. Rewrite using `[Scheme.preimage_basicOpen]`. Establish `: C.basicOpen ((e.app ⊤).hom f) = ⊤` using `Scheme.basicOpen_of_isUnit _ hf`.

Rewrite using `[this]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hx`. Set `e' : C ⟶ (D.basicOpen f).toScheme` to `IsOpenImmersion.lift _ e hr`.

Establish `he' : e' ≫ (D.basicOpen f).ι = e` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hq` using `isPullback_morphismRestrict p (D.basicOpen f)`. Establish `hw : (s ≫ e') ≫ (D.basicOpen f).ι = u ≫ p`. Rewrite using `[Category.assoc, he', h.w]`. Set `t` to `hq.lift (s ≫ e') u hw`.

Establish `ht1 : t ≫ (p ∣_ D.basicOpen f) = s ≫ e'` using `hq.lift_fst _ _ _`. Establish `ht2 : t ≫ (p ⁻¹ᵁ D.basicOpen f).ι = u` using `hq.lift_snd _ _ _`. Establish `hpb : IsPullback t s (p ∣_ D.basicOpen f) e'`. Use `IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ D.basicOpen f).ι) (h₂₂ := (D.basicOpen f).ι) (v₁₃ := p) ?_ ht1 hq.flip` and prove the remaining obligations. Rewrite using `[ht2, he']`.

Conclude with `h`. Conclude with `et_of_pb hpb`.
-/
private theorem et_of_restrict {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) (f : Γ(D, ⊤)) (hf : IsUnit (e.appTop f)) (he : Etale (p ∣_ D.basicOpen f)) : Etale s := by
  have hr : Set.range e ⊆ Set.range (D.basicOpen f).ι := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ e ⁻¹ᵁ D.basicOpen f := by
      rw [Scheme.preimage_basicOpen]
      have : C.basicOpen ((e.app ⊤).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hf
      rw [this]; trivial
    rw [Scheme.Opens.range_ι]
    exact hx
  let e' : C ⟶ (D.basicOpen f).toScheme := IsOpenImmersion.lift _ e hr
  have he' : e' ≫ (D.basicOpen f).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hq := isPullback_morphismRestrict p (D.basicOpen f)
  have hw : (s ≫ e') ≫ (D.basicOpen f).ι = u ≫ p := by
    rw [Category.assoc, he', h.w]
  let t := hq.lift (s ≫ e') u hw
  have ht1 : t ≫ (p ∣_ D.basicOpen f) = s ≫ e' := hq.lift_fst _ _ _
  have ht2 : t ≫ (p ⁻¹ᵁ D.basicOpen f).ι = u := hq.lift_snd _ _ _
  have hpb : IsPullback t s (p ∣_ D.basicOpen f) e' := by
    refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ D.basicOpen f).ι) (h₂₂ := (D.basicOpen f).ι) (v₁₃ := p) ?_ ht1 hq.flip
    rw [ht2, he']
    exact h
  exact et_of_pb hpb

end UpperTheory.Gal.Mod.BaseChangeExamples

open UpperTheory.Gal.Mod.BaseChangeExamples in
/- English proof (translation)
Introduce `p O k Ω _ _ _ _ _ hp Y g T hg`. Set `q` to `pullback.snd g (sp (algebraMap O k))`. Set `s : geom Ω q ⟶ Y` to `pullback.fst _ _ ≫ pullback.fst _ _`. Establish `h : IsPullback (pullback.fst T.p s) (pullback.snd T.p s) T.p s` using `IsPullback.of_hasPullback T.p s`. Establish `hfin : IsFinite (pullback.snd T.p s)`.

Use `T.fin` as an intermediate fact. Use `infer_instance`. Establish `het : Etale (pullback.snd T.p s)` using `et_of_restrict h (p : Γ(Y, ⊤)) (by simpa using isUnit_nat (pullback.fst q (sp (algebraMap k Ω)) ≫ q) p hp) T.et`. Establish `c1 : (pullback.fst T.p s ≫ T.r) ≫ g = (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) ≫ sp (algebraMap O k)`. Establish `e1 : pullback.fst T.p s ≫ T.p = pullback.snd T.p s ≫ s` using `h.w`.

Establish `e2 : pullback.fst g (sp (algebraMap O k)) ≫ g = q ≫ sp (algebraMap O k)` using `pullback.condition`. Rewrite using `[Category.assoc, hg, reassoc_of% e1]`. Simplify using `only [s, Category.assoc, e2]`. Set `a : pullback T.p s ⟶ pullback g (sp (algebraMap O k))` to `pullback.lift (pullback.fst T.p s ≫ T.r) (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) c1`. Establish `ha1 : a ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r` using `pullback.lift_fst _ _ _`.

Establish `ha2 : a ≫ q = pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q` using `pullback.lift_snd _ _ _`. Establish `c2 : a ≫ q = (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) ≫ sp (algebraMap k Ω)`. Establish `e3 : pullback.fst q (sp (algebraMap k Ω)) ≫ q = pullback.snd q (sp (algebraMap k Ω)) ≫ sp (algebraMap k Ω)` using `pullback.condition`. Rewrite using `[ha2, e3, Category.assoc]`. Set `b : pullback T.p s ⟶ geom Ω q` to `pullback.lift a (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) c2`.

Establish `hb1 : b ≫ pullback.fst q (sp (algebraMap k Ω)) = a` using `pullback.lift_fst _ _ _`. Establish `hb2 : b ≫ pullback.snd q (sp (algebraMap k Ω)) = pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))` using `pullback.lift_snd _ _ _`. Use `⟨⟨pullback T.p s, pullback.snd T.p s, b, Wt.const _ 1, hfin, isWt_one _⟩, pullback.fst T.p s, h, ?_, hb2, rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `b ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r`. Rewrite using `[reassoc_of% hb1, ha1]`.
-/
theorem UpperTheory.Gal.Mod.bcEx :
    BCEx := by
  intro p O k Ω _ _ _ _ _ hp Y g T hg
  let q := pullback.snd g (sp (algebraMap O k))
  let s : geom Ω q ⟶ Y := pullback.fst _ _ ≫ pullback.fst _ _
  have h : IsPullback (pullback.fst T.p s) (pullback.snd T.p s) T.p s := IsPullback.of_hasPullback T.p s
  have hfin : IsFinite (pullback.snd T.p s) := by
    have := T.fin
    infer_instance
  have het : Etale (pullback.snd T.p s) :=
    et_of_restrict h (p : Γ(Y, ⊤)) (by simpa using isUnit_nat (pullback.fst q (sp (algebraMap k Ω)) ≫ q) p hp) T.et
  have c1 : (pullback.fst T.p s ≫ T.r) ≫ g =
      (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) ≫ sp (algebraMap O k) := by
    have e1 : pullback.fst T.p s ≫ T.p = pullback.snd T.p s ≫ s := h.w
    have e2 : pullback.fst g (sp (algebraMap O k)) ≫ g = q ≫ sp (algebraMap O k) := pullback.condition
    rw [Category.assoc, hg, reassoc_of% e1]
    simp only [s, Category.assoc, e2]
  let a : pullback T.p s ⟶ pullback g (sp (algebraMap O k)) :=
    pullback.lift (pullback.fst T.p s ≫ T.r) (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) c1
  have ha1 : a ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r := pullback.lift_fst _ _ _
  have ha2 : a ≫ q = pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q := pullback.lift_snd _ _ _
  have c2 : a ≫ q = (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) ≫ sp (algebraMap k Ω) := by
    have e3 : pullback.fst q (sp (algebraMap k Ω)) ≫ q = pullback.snd q (sp (algebraMap k Ω)) ≫ sp (algebraMap k Ω) :=
      pullback.condition
    rw [ha2, e3, Category.assoc]
  let b : pullback T.p s ⟶ geom Ω q := pullback.lift a (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) c2
  have hb1 : b ≫ pullback.fst q (sp (algebraMap k Ω)) = a := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd q (sp (algebraMap k Ω)) = pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω)) :=
    pullback.lift_snd _ _ _
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, b, Wt.const _ 1, hfin, isWt_one _⟩, pullback.fst T.p s, h, ?_, hb2, rfl⟩
  change b ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r
  rw [reassoc_of% hb1, ha1]
