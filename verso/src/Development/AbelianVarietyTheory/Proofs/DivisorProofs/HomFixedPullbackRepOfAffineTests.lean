import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S H : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {AH BH : Over H} [GrpObj AH] [GrpObj BH]

def IsSol (π : H ⟶ S) (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH) {T : Scheme.{0}} (t : T ⟶ S)
    (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (h : T ⟶ H) : Prop :=
  h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
    IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

def IsRestr {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B')
    {A'' B'' : Over U} [GrpObj A''] [GrpObj B''] (Φ'' : A'' ⟶ B'') (ρA : A''.left ⟶ A'.left)
    (ρB : B''.left ⟶ B'.left) : Prop :=
  IsGrpPullback A'' A' g ρA ∧ IsGrpPullback B'' B' g ρB ∧ Φ''.left ≫ ρB = ρA ≫ Φ'.left

variable {π : H ⟶ S} {φA : AH.left ⟶ A.left} {φB : BH.left ⟶ B.left} {Φ : AH ⟶ BH}

/- English proof (translation)
Assemble the required witnesses or components as `⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩`.
-/
theorem isRestr_pullback {T U : Scheme.{0}} (g : U ⟶ T) {A' B' : Over T} [GrpObj A'] [GrpObj B'] (Φ' : A' ⟶ B') :
    IsRestr g Φ' ((Over.pullback g).map Φ') (pullback.fst A'.hom g) (pullback.fst B'.hom g) :=
  ⟨isGrpPullback_pullback A' g, isGrpPullback_pullback B' g, pullback.lift_fst _ _ _⟩

/- English proof (translation)
Take `⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩` from `hs`. Take `⟨rA, rB, rΦ⟩` from `hr`. Use `⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA], by rw [Category.assoc, eB], ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]`.
-/
theorem IsSol.restr {T U : Scheme.{0}} {t : T ⟶ S} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {h : T ⟶ H}
    (hs : IsSol π φA φB Φ t A' B' φA' φB' Φ' h) {g : U ⟶ T} {A'' B'' : Over U} [GrpObj A''] [GrpObj B'']
    {Φ'' : A'' ⟶ B''} {ρA : A''.left ⟶ A'.left} {ρB : B''.left ⟶ B'.left} (hr : IsRestr g Φ' Φ'' ρA ρB) :
    IsSol π φA φB Φ (g ≫ t) A'' B'' (ρA ≫ φA') (ρB ≫ φB') Φ'' (g ≫ h) := by
  obtain ⟨h1, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs
  obtain ⟨rA, rB, rΦ⟩ := hr
  refine ⟨by rw [Category.assoc, h1], ρA ≫ ψA, ρB ≫ ψB, rA.comp pA, rB.comp pB, by rw [Category.assoc, eA],
    by rw [Category.assoc, eB], ?_⟩
  rw [← Category.assoc, rΦ, Category.assoc, eΦ, Category.assoc]

/- English proof (translation)
Take `⟨aα, bα, cα⟩` from `hα`. Take `⟨aW, bW, cW⟩` from `hW`. Establish `wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f` using `by rw [aW.1.w, Category.assoc]`. Establish `wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f` using `by rw [bW.1.w, Category.assoc]`. Use `⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm) (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩, aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩` and prove the remaining obligations.

Apply `bα.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]`.
-/
theorem IsRestr.factor {T U W : Scheme.{0}} {f : U ⟶ T} {k : W ⟶ U} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα] {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left}
    {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {AW BW : Over W} [GrpObj AW] [GrpObj BW]
    {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left} (hW : IsRestr (k ≫ f) Φ' ΦW ρAW ρBW) :
    ∃ (σA : AW.left ⟶ Aα.left) (σB : BW.left ⟶ Bα.left), IsRestr k Φα ΦW σA σB ∧ σA ≫ ρAα = ρAW ∧
      σB ≫ ρBα = ρBW := by
  obtain ⟨aα, bα, cα⟩ := hα
  obtain ⟨aW, bW, cW⟩ := hW
  have wA : ρAW ≫ A'.hom = (AW.hom ≫ k) ≫ f := by rw [aW.1.w, Category.assoc]
  have wB : ρBW ≫ B'.hom = (BW.hom ≫ k) ≫ f := by rw [bW.1.w, Category.assoc]
  refine ⟨aα.1.lift _ _ wA, bα.1.lift _ _ wB, ⟨aα.cancel (aW.congr rfl (aα.1.lift_fst _ _ wA).symm)
    (aα.1.lift_snd _ _ wA), bα.cancel (bW.congr rfl (bα.1.lift_fst _ _ wB).symm) (bα.1.lift_snd _ _ wB), ?_⟩,
    aα.1.lift_fst _ _ wA, bα.1.lift_fst _ _ wB⟩
  apply bα.1.hom_ext
  · rw [Category.assoc, Category.assoc, bα.1.lift_fst, cW, cα, ← Category.assoc, aα.1.lift_fst]
  · rw [Category.assoc, Category.assoc, bα.1.lift_snd, Over.w Φα, aα.1.lift_snd, ← Category.assoc, Over.w ΦW]

/- English proof (translation)
Substitute `hg` using the available equality. Take `⟨σA, σB, hr, eA, eB⟩` from `hα.factor hW`. Use `hs.restr hr` as an intermediate fact. Rewrite using `[← eA, ← eB]`. Simplify using `only [Category.assoc] at this ⊢`.

Conclude with `this`.
-/
theorem IsSol.pull {T U W : Scheme.{0}} {t : T ⟶ S} {f : U ⟶ T} {A' B' : Over T} [GrpObj A'] [GrpObj B']
    {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {Aα Bα : Over U} [GrpObj Aα] [GrpObj Bα]
    {Φα : Aα ⟶ Bα} {ρAα : Aα.left ⟶ A'.left} {ρBα : Bα.left ⟶ B'.left} (hα : IsRestr f Φ' Φα ρAα ρBα) {hα' : U ⟶ H}
    (hs : IsSol π φA φB Φ (f ≫ t) Aα Bα (ρAα ≫ φA') (ρBα ≫ φB') Φα hα') (k : W ⟶ U) {g : W ⟶ T} (hg : g = k ≫ f)
    {AW BW : Over W} [GrpObj AW] [GrpObj BW] {ΦW : AW ⟶ BW} {ρAW : AW.left ⟶ A'.left} {ρBW : BW.left ⟶ B'.left}
    (hW : IsRestr g Φ' ΦW ρAW ρBW) : IsSol π φA φB Φ (g ≫ t) AW BW (ρAW ≫ φA') (ρBW ≫ φB') ΦW (k ≫ hα') := by
  subst hg
  obtain ⟨σA, σB, hr, eA, eB⟩ := hα.factor hW
  have := hs.restr hr
  rw [← eA, ← eB]
  simp only [Category.assoc] at this ⊢
  exact this

/- English proof (translation)
Establish `wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π` using `by rw [hA.1.w, Category.assoc, hh]`. Establish `wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π` using `by rw [hB.1.w, Category.assoc, hh]`. Use `⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB, pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA), pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB), pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩` and prove the remaining obligations. Take `⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩` from `hs i`. Take `⟨rA, rB, rΦ⟩` from `hr i`.

Establish `hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA` using `pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst]) (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])`. Establish `hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB` using `pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst]) (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])`. Rewrite using `[← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]`.
-/
theorem isSol_of_local (pbA : IsGrpPullback AH A π φA) (pbB : IsGrpPullback BH B π φB) {T : Scheme.{0}} {t : T ⟶ S}
    {A' B' : Over T} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'}
    (hA : IsGrpPullback A' A t φA') (hB : IsGrpPullback B' B t φB') {h : T ⟶ H} (hh : h ≫ π = t) {Idx : Type}
    {U : Idx → Scheme.{0}} (f : ∀ i, U i ⟶ T) (Aα Bα : ∀ i, Over (U i)) [∀ i, GrpObj (Aα i)] [∀ i, GrpObj (Bα i)]
    (Φα : ∀ i, Aα i ⟶ Bα i) (ρA : ∀ i, (Aα i).left ⟶ A'.left) (ρB : ∀ i, (Bα i).left ⟶ B'.left)
    (hr : ∀ i, IsRestr (f i) Φ' (Φα i) (ρA i) (ρB i))
    (hs : ∀ i, IsSol π φA φB Φ (f i ≫ t) (Aα i) (Bα i) (ρA i ≫ φA') (ρB i ≫ φB') (Φα i) (f i ≫ h))
    (hepi : ∀ (u v : A'.left ⟶ BH.left), (∀ i, ρA i ≫ u = ρA i ≫ v) → u = v) :
    IsSol π φA φB Φ t A' B' φA' φB' Φ' h := by
  have wA : φA' ≫ A.hom = (A'.hom ≫ h) ≫ π := by rw [hA.1.w, Category.assoc, hh]
  have wB : φB' ≫ B.hom = (B'.hom ≫ h) ≫ π := by rw [hB.1.w, Category.assoc, hh]
  refine ⟨hh, pbA.1.lift _ _ wA, pbB.1.lift _ _ wB,
    pbA.cancel (hA.congr hh.symm (pbA.1.lift_fst _ _ wA).symm) (pbA.1.lift_snd _ _ wA),
    pbB.cancel (hB.congr hh.symm (pbB.1.lift_fst _ _ wB).symm) (pbB.1.lift_snd _ _ wB),
    pbA.1.lift_fst _ _ wA, pbB.1.lift_fst _ _ wB, hepi _ _ fun i => ?_⟩
  obtain ⟨-, ψA, ψB, pA, pB, eA, eB, eΦ⟩ := hs i
  obtain ⟨rA, rB, rΦ⟩ := hr i
  have hψA : ψA = ρA i ≫ pbA.1.lift _ _ wA := pbA.1.hom_ext (by rw [eA, Category.assoc, pbA.1.lift_fst])
    (by rw [pA.1.w, Category.assoc, pbA.1.lift_snd, ← Category.assoc (ρA i), rA.1.w, Category.assoc])
  have hψB : ψB = ρB i ≫ pbB.1.lift _ _ wB := pbB.1.hom_ext (by rw [eB, Category.assoc, pbB.1.lift_fst])
    (by rw [pB.1.w, Category.assoc, pbB.1.lift_snd, ← Category.assoc (ρB i), rB.1.w, Category.assoc])
  rw [← Category.assoc, ← rΦ, Category.assoc, ← hψB, eΦ, hψA, Category.assoc]

/- English proof (translation)
Establish `hN` using `pull_isLB hM φB'`. Establish `i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB))` using `GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso`. Establish `i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l)` using `GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl`. Establish `i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l)` using `GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l`. Conclude with `LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1 (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)`.
-/
theorem lbIso_restr {XA XB A'l B'l A''l B''l : Scheme.{0}} {L : LB XA} {M : LB XB} (hL : L.IsLB) (hM : M.IsLB)
    {φA' : A'l ⟶ XA} {φB' : B'l ⟶ XB} {Φl : A'l ⟶ B'l} {ρA : A''l ⟶ A'l} {ρB : B''l ⟶ B'l} {Φ''l : A''l ⟶ B''l}
    (e : Φ''l ≫ ρB = ρA ≫ Φl) (iso : LBIso (L.pull φA') ((M.pull φB').pull Φl)) :
    LBIso (L.pull (ρA ≫ φA')) ((M.pull (ρB ≫ φB')).pull Φ''l) := by
  have hN := pull_isLB hM φB'
  have i1 : LBIso (L.pull (ρA ≫ φA')) ((M.pull φB').pull (Φ''l ≫ ρB)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp ρA rfl e iso
  have i2 : LBIso ((M.pull φB').pull (Φ''l ≫ ρB)) (((M.pull φB').pull ρB).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hN Φ''l rfl
  have i3 : LBIso (((M.pull φB').pull ρB).pull Φ''l) ((M.pull (ρB ≫ φB')).pull Φ''l) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hM ρB rfl)) Φ''l
  exact LBIso.trans (pull_isLB hL _) (pull_isLB hN _) (pull_isLB (pull_isLB hM _) _) i1
    (LBIso.trans (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) (pull_isLB (pull_isLB hM _) _) i2 i3)

/- English proof (translation)
Introduce `S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso`. Establish `key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB') ((Over.pullback f).map Φ') k` using `fun R _ f => haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ') ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)`. Set `𝒜` to `T.affineOpenCover`. Set `𝒰` to `𝒜.openCover`. Establish `hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A') ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB') ((Over.pullback (𝒰.f i)).map Φ') k` using `fun i => key (𝒜.X i) (𝒰.f i)`.

Use `choose k hk hku using hloc`. Establish `hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j`. Introduce `i j`. Set `𝒲` to `(pullback (𝒰.f i) (𝒰.f j)).affineOpenCover`. Use `𝒲.openCover.hom_ext _ _ fun l => ?_` and prove the remaining obligations.

Set `g : Sp (𝒲.X l) ⟶ T` to `(𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i`. Establish `hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j` using `(Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)`. Establish `hu` using `key (𝒲.X l) g`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Conclude with `hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ')) (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))`.

Set `hg` to `𝒰.glueMorphisms k hagree`. Establish `hι : ∀ i, 𝒰.f i ≫ hg = k i` using `𝒰.ι_glueMorphisms k hagree`. Establish `hh : hg ≫ π = t` using `𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1`. Establish `hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg` using `isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A') (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ') (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i)) (fun i => isRestr_pullback _ Φ') (fun i …`. Use `⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hι]`. Conclude with `hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))`.
-/
theorem rep_of_affine : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB →
  ∀ (H : Scheme.{0}) (π : H ⟶ S) (AH : Over H) [GrpObj AH] (BH : Over H) [GrpObj BH]
    (φA : AH.left ⟶ A.left) (φB : BH.left ⟶ B.left) (Φ : AH ⟶ BH),
    IsGrpPullback AH A π φA → IsGrpPullback BH B π φB →
    (∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : Sp R ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left) →
    ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
      (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
      LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
      ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
        IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left := by
  intro S A B _ _ L M hL hM H π AH _ BH _ φA φB Φ pbA pbB haff T t A' B' _ _ φA' φB' Φ' hA hB hΦ iso
  have key : ∀ (R : Type) [CommRing R] (f : Sp R ⟶ T), ∃! k : Sp R ⟶ H, IsSol π φA φB Φ (f ≫ t)
      ((Over.pullback f).obj A') ((Over.pullback f).obj B') (pullback.fst A'.hom f ≫ φA') (pullback.fst B'.hom f ≫ φB')
      ((Over.pullback f).map Φ') k := fun R _ f =>
    haff R (f ≫ t) ((Over.pullback f).obj A') ((Over.pullback f).obj B') _ _ ((Over.pullback f).map Φ')
      ((isRestr_pullback f Φ').1.comp hA) ((isRestr_pullback f Φ').2.1.comp hB) inferInstance
      (lbIso_restr hL hM (isRestr_pullback f Φ').2.2 iso)
  let 𝒜 := T.affineOpenCover
  let 𝒰 := 𝒜.openCover
  have hloc : ∀ i, ∃! k : 𝒰.X i ⟶ H, IsSol π φA φB Φ (𝒰.f i ≫ t) ((Over.pullback (𝒰.f i)).obj A')
      ((Over.pullback (𝒰.f i)).obj B') (pullback.fst A'.hom (𝒰.f i) ≫ φA') (pullback.fst B'.hom (𝒰.f i) ≫ φB')
      ((Over.pullback (𝒰.f i)).map Φ') k := fun i => key (𝒜.X i) (𝒰.f i)
  choose k hk hku using hloc
  have hagree : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    intro i j
    let 𝒲 := (pullback (𝒰.f i) (𝒰.f j)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun l => ?_
    let g : Sp (𝒲.X l) ⟶ T := (𝒲.openCover.f l ≫ pullback.fst _ _) ≫ 𝒰.f i
    have hg : g = (𝒲.openCover.f l ≫ pullback.snd _ _) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (𝒲.openCover.f l ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    have hu := key (𝒲.X l) g
    rw [← Category.assoc, ← Category.assoc]
    exact hu.unique (IsSol.pull (isRestr_pullback _ Φ') (hk i) _ rfl (isRestr_pullback g Φ'))
      (IsSol.pull (isRestr_pullback _ Φ') (hk j) _ hg (isRestr_pullback g Φ'))
  let hg := 𝒰.glueMorphisms k hagree
  have hι : ∀ i, 𝒰.f i ≫ hg = k i := 𝒰.ι_glueMorphisms k hagree
  have hh : hg ≫ π = t := 𝒰.hom_ext _ _ fun i => by rw [← Category.assoc, hι]; exact (hk i).1
  have hsol : IsSol π φA φB Φ t A' B' φA' φB' Φ' hg :=
    isSol_of_local pbA pbB hA hB hh 𝒰.f (fun i => (Over.pullback (𝒰.f i)).obj A')
      (fun i => (Over.pullback (𝒰.f i)).obj B') (fun i => (Over.pullback (𝒰.f i)).map Φ')
      (fun i => pullback.fst A'.hom (𝒰.f i)) (fun i => pullback.fst B'.hom (𝒰.f i))
      (fun i => isRestr_pullback _ Φ') (fun i => by rw [hι]; exact hk i)
      (fun u v h => Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁ A'.hom 𝒰) u v h)
  refine ⟨hg, hsol, fun h' hs' => 𝒰.hom_ext _ _ fun i => ?_⟩
  rw [hι]
  exact hku i _ (IsSol.restr hs' (isRestr_pullback _ Φ'))

end GlobalTheory.EndLoc.HomFixGlue
