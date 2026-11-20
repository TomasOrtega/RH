import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPointsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Use `haveI := hfin`. Use `haveI := hfl`. Establish `hcF : ((c : FractionRing V)) ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Apply `IsFractionRing.injective V (FractionRing V)` to reduce the goal to its premises. Simplify using `using h`. Set `pt : Sp (FractionRing V)` to `(⊥ : PrimeSpectrum (FractionRing V))`. Establish `h1` using `GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points S A hab K i c hm hfin hfl hi (FractionRing V) hcF (spMap (algebraMap V (FractionRing V)) ≫ z) pt`. Establish `h2` using `Scheme.Hom.finrank_of_isPullback k (spMap (algebraMap V B)) K.hom z hk (spMap (algebraMap V (FractionRing V)) pt)`.

Establish `h3` using `Scheme.Hom.finrank_SpecMap_algebraMap V B (spMap (algebraMap V (FractionRing V)) pt)`. Rewrite `h1` using `[Scheme.Hom.comp_apply]`. Establish `h4 : Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} = Nat.card (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ K)`. Use `Nat.card_congr (Equiv.ofBijective (fun g => ⟨g ≫ i, (hP _ _).1 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩).symm` and prove the remaining obligations. Introduce `a b hab'`.

Conclude with `(cancel_mono i).1 (congrArg Subtype.val hab')`. Introduce and unpack `⟨g, hg⟩`. Take `⟨y, hy⟩` from `(hP _ _).2 hg`. Conclude with `⟨y, Subtype.ext hy⟩`. Rewrite using `[h4, ← h1, ← h2]`.

Unfold `spMap at h3 ⊢`. Rewrite using `[h3, Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression.
-/
private theorem count_eq (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (hab : IsAbelianScheme A)
    (K : Over S) (i : K ⟶ A) (hm : Mono i) (hfin : IsFinite K.hom) (hfl : Flat K.hom) (c : ℕ) (hi : i ^ c = 1)
    (P : ∀ T : Over S, (T ⟶ A) → Prop) (hP : ∀ (T : Over S) (g : T ⟶ A), InSub i g ↔ P T g)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (hc : (c : V) ≠ 0)
    (z : Sp V ⟶ S) (B : Type) [CommRing B] [Algebra V B] [Module.Finite V B] [Module.Free V B] (k : Sp B ⟶ K.left)
    (hk : IsPullback k (spMap (algebraMap V B)) K.hom z) :
    Module.finrank V B = Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} := by
  haveI := hfin
  haveI := hfl
  have hcF : ((c : FractionRing V)) ≠ 0 := by
    intro h
    apply hc
    apply IsFractionRing.injective V (FractionRing V)
    simpa using h
  let pt : Sp (FractionRing V) := (⊥ : PrimeSpectrum (FractionRing V))
  have h1 := GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points S A hab K i c hm hfin hfl hi (FractionRing V) hcF
    (spMap (algebraMap V (FractionRing V)) ≫ z) pt
  have h2 := Scheme.Hom.finrank_of_isPullback k (spMap (algebraMap V B)) K.hom z hk
    (spMap (algebraMap V (FractionRing V)) pt)
  have h3 := Scheme.Hom.finrank_SpecMap_algebraMap V B (spMap (algebraMap V (FractionRing V)) pt)
  rw [Scheme.Hom.comp_apply] at h1
  have h4 : Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} =
      Nat.card (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ K) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g ≫ i, (hP _ _).1 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩).symm
    · intro a b hab'
      exact (cancel_mono i).1 (congrArg Subtype.val hab')
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hP _ _).2 hg
      exact ⟨y, Subtype.ext hy⟩
  rw [h4, ← h1, ← h2]
  unfold spMap at h3 ⊢
  rw [h3, Module.rankAtStalk_eq_finrank_of_free]
  rfl

/- English proof (translation)
Introduce `hAlg S A _ _ hab P hRep c hc V _ _ _ _ hcV z A' φ hpb P' hP'`. Take `⟨K, i, hm, hfin, hfl, hiP⟩` from `hRep`. Use `haveI := hfin`. Use `haveI := hfl`. Establish `hi : i ^ c = 1` using `hc K i ((hiP K i).1 ⟨𝟙 _, by simp⟩)`.

Take `⟨BV, _, _, kV, _, _, hkV⟩` from `hAlg S K.left K.hom hfin hfl V z`. Establish `hcount` using `count_eq S A hab K i hm hfin hfl c hi P hiP V hcV z BV kV hkV`. Take `⟨Bk, _, _, kk, _, _, hkk⟩` from `hAlg S K.left K.hom hfin hfl (IsLocalRing.ResidueField V) (resPt V ≫ z)`. Establish `hr : Module.finrank (IsLocalRing.ResidueField V) Bk = Module.finrank V BV`. Set `q : Sp (IsLocalRing.ResidueField V)` to `(⊥ : PrimeSpectrum (IsLocalRing.ResidueField V))`.

Establish `e1` using `Scheme.Hom.finrank_of_isPullback kk _ K.hom (resPt V ≫ z) hkk q`. Establish `e2` using `Scheme.Hom.finrank_of_isPullback kV _ K.hom z hkV (resPt V q)`. Establish `e3` using `Scheme.Hom.finrank_SpecMap_algebraMap (IsLocalRing.ResidueField V) Bk q`. Establish `e4` using `Scheme.Hom.finrank_SpecMap_algebraMap V BV (resPt V q)`. Rewrite `e1` using `[Scheme.Hom.comp_apply]`.

Unfold `spMap at e1 e2`. Rewrite `e1` using `[e3, Module.rankAtStalk_eq_finrank_of_free]`. Rewrite `e2` using `[e4, Module.rankAtStalk_eq_finrank_of_free]`. Conclude with `e1.trans e2.symm`. Establish `wsq : (kk ≫ i.left) ≫ A.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) ≫ (resPt V ≫ z)`.

Rewrite using `[Category.assoc, Over.w i]`. Conclude with `hkk.w`. Establish `hlf : hpb.lift _ _ wsq ≫ φ = kk ≫ i.left` using `hpb.lift_fst _ _ wsq`. Establish `hls : hpb.lift _ _ wsq ≫ A'.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk)` using `hpb.lift_snd _ _ wsq`. Establish `hlm : Mono (hpb.lift _ _ wsq)`.

Prove the components needed by the constructor for the conclusion. Introduce `X a b hab'`. Apply `hkk.hom_ext` to reduce the goal to its premises. Use `haveI := Over.mono_left_of_mono i`. Establish `h1` using `congrArg (· ≫ φ) hab'`.

Simplify using `only [Category.assoc, hlf] at h1`. Simplify `(cancel_mono i.left).1 (by simpa only [Category.assoc] using h1)` using `only [Category.assoc]`. Establish `h1` using `congrArg (· ≫ A'.hom) hab'`. Simplify `h1` using `only [Category.assoc, hls]`. Use `⟨Bk, inferInstance, inferInstance, inferInstance, inferInstance, hr.trans hcount, Over.homMk (U := Over.mk (spMap (algebraMap (IsLocalRing.ResidueField V) Bk))) (hpb.lift _ _ wsq) hls, ?_, ?_⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `X a b hab'`. Use `ext`. Conclude with `(cancel_mono (hpb.lift _ _ wsq)).1 (by simpa using congrArg Over.Hom.left hab')`. Introduce `T g`.

Establish `hw : (g.left ≫ φ) ≫ A.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom`. Rewrite using `[Category.assoc, hpb.w, ← Category.assoc, Over.w g]`. Both sides reduce to the same expression. Rewrite using `[hP' T g (Over.homMk (g.left ≫ φ) hw) rfl, ← hiP]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy⟩`. Establish `hyl` using `congrArg Over.Hom.left hy`. Simplify using `only [Over.comp_left, Over.homMk_left] at hyl`. Establish `hw2 : (y.left ≫ kk) ≫ K.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom`. Rewrite using `[Category.assoc, hkk.w]`.

Simplify using `using congrArg (· ≫ resPt V ≫ z) (Over.w y)`. Use `⟨Over.homMk (y.left ≫ kk) hw2, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left, Category.assoc]`. Rewrite using `[← hyl, Category.assoc, hlf]`.

Introduce and unpack `⟨y, hy⟩`. Establish `hyl` using `congrArg Over.Hom.left hy`. Simplify using `only [Over.comp_left, Over.homMk_left] at hyl`. Establish `hw3 : y.left ≫ K.hom = T.hom ≫ resPt V ≫ z`. Simplify using `using Over.w y`.

Use `⟨Over.homMk (hkk.lift y.left T.hom hw3) (by simpa using hkk.lift_snd _ _ hw3), ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [Over.comp_left, Over.homMk_left]`. Apply `hpb.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hlf, ← Category.assoc, hkk.lift_fst, hyl]`.

Rewrite using `[Category.assoc, hls, hkk.lift_snd]`. Simplify using `using (Over.w g).symm`.
-/
theorem fFRead_of : AlgOf → FFRead := by
  intro hAlg S A _ _ hab P hRep c hc V _ _ _ _ hcV z A' φ hpb P' hP'
  obtain ⟨K, i, hm, hfin, hfl, hiP⟩ := hRep
  haveI := hfin
  haveI := hfl
  have hi : i ^ c = 1 := hc K i ((hiP K i).1 ⟨𝟙 _, by simp⟩)
  obtain ⟨BV, _, _, kV, _, _, hkV⟩ := hAlg S K.left K.hom hfin hfl V z
  have hcount := count_eq S A hab K i hm hfin hfl c hi P hiP V hcV z BV kV hkV
  obtain ⟨Bk, _, _, kk, _, _, hkk⟩ :=
    hAlg S K.left K.hom hfin hfl (IsLocalRing.ResidueField V) (resPt V ≫ z)
  have hr : Module.finrank (IsLocalRing.ResidueField V) Bk = Module.finrank V BV := by
    let q : Sp (IsLocalRing.ResidueField V) := (⊥ : PrimeSpectrum (IsLocalRing.ResidueField V))
    have e1 := Scheme.Hom.finrank_of_isPullback kk _ K.hom (resPt V ≫ z) hkk q
    have e2 := Scheme.Hom.finrank_of_isPullback kV _ K.hom z hkV (resPt V q)
    have e3 := Scheme.Hom.finrank_SpecMap_algebraMap (IsLocalRing.ResidueField V) Bk q
    have e4 := Scheme.Hom.finrank_SpecMap_algebraMap V BV (resPt V q)
    rw [Scheme.Hom.comp_apply] at e1
    unfold spMap at e1 e2
    rw [e3, Module.rankAtStalk_eq_finrank_of_free] at e1
    rw [e4, Module.rankAtStalk_eq_finrank_of_free] at e2
    exact e1.trans e2.symm
  have wsq : (kk ≫ i.left) ≫ A.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) ≫ (resPt V ≫ z) := by
    rw [Category.assoc, Over.w i]
    exact hkk.w
  have hlf : hpb.lift _ _ wsq ≫ φ = kk ≫ i.left := hpb.lift_fst _ _ wsq
  have hls : hpb.lift _ _ wsq ≫ A'.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) :=
    hpb.lift_snd _ _ wsq
  have hlm : Mono (hpb.lift _ _ wsq) := by
    constructor
    intro X a b hab'
    apply hkk.hom_ext
    · haveI := Over.mono_left_of_mono i
      have h1 := congrArg (· ≫ φ) hab'
      simp only [Category.assoc, hlf] at h1
      simpa only [Category.assoc] using (cancel_mono i.left).1 (by simpa only [Category.assoc] using h1)
    · have h1 := congrArg (· ≫ A'.hom) hab'
      simpa only [Category.assoc, hls] using h1
  refine ⟨Bk, inferInstance, inferInstance, inferInstance, inferInstance, hr.trans hcount,
    Over.homMk (U := Over.mk (spMap (algebraMap (IsLocalRing.ResidueField V) Bk))) (hpb.lift _ _ wsq) hls,
    ?_, ?_⟩
  · constructor
    intro X a b hab'
    ext
    exact (cancel_mono (hpb.lift _ _ wsq)).1 (by simpa using congrArg Over.Hom.left hab')
  · intro T g
    have hw : (g.left ≫ φ) ≫ A.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w g]
      rfl
    rw [hP' T g (Over.homMk (g.left ≫ φ) hw) rfl, ← hiP]
    constructor
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw2 : (y.left ≫ kk) ≫ K.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
        rw [Category.assoc, hkk.w]
        simpa using congrArg (· ≫ resPt V ≫ z) (Over.w y)
      refine ⟨Over.homMk (y.left ≫ kk) hw2, ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [← hyl, Category.assoc, hlf]
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw3 : y.left ≫ K.hom = T.hom ≫ resPt V ≫ z := by
        simpa using Over.w y
      refine ⟨Over.homMk (hkk.lift y.left T.hom hw3) (by simpa using hkk.lift_snd _ _ hw3), ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left]
      apply hpb.hom_ext
      · rw [Category.assoc, hlf, ← Category.assoc, hkk.lift_fst, hyl]
      · rw [Category.assoc, hls, hkk.lift_snd]
        simpa using (Over.w g).symm

end UpperTheory.Gal.crystallineComparison.Mod
