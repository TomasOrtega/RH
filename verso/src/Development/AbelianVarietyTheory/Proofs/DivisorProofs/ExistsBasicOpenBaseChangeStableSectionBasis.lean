import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjByOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HomFixLocBasis

/- English proof (translation)
Introduce `S S' u A Ag φ hφ R _ x y hxy h h1 h2`. Substitute `hxy` using the available equality. Establish `P` using `(GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ`. Establish `Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u)` using `GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))`. Establish `P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u)` using `P`.

Establish `e : h = (P'.isoIsPullback _ _ Q).hom` using `Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)`. Rewrite using `[e]`. Use `infer_instance`.
-/
theorem isIso_compare : ∀ {S S' : Scheme.{0}} (u : S' ⟶ S) (A : Over S) (Ag : Over S') (φ : Ag.left ⟶ A.left), IsPullback φ Ag.hom A.hom u → ∀ (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S), x ≫ u = y → ∀ (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left), h ≫ (snd (Over.mk y) A).left = (snd (Over.mk x) Ag).left ≫ φ → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → IsIso h := by
  intro S S' u A Ag φ hφ R _ x y hxy h h1 h2
  subst hxy
  have P := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ
  have Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u) :=
    GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))
  have P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u) := P
  have e : h = (P'.isoIsPullback _ _ Q).hom :=
    Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)
  rw [e]
  infer_instance

/- English proof (translation)
Establish `hVo : IsOpen (X` using `PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen`. Establish `hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg))` using `hpV`. Take `⟨W, ⟨f, rfl⟩, h1, h2⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo`. Conclude with `⟨f, h1, h2⟩`.
-/
theorem exists_basicOpen_le {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (p : Sp Rg) (hpV : p ∈ V) :
    ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg))) := by
  have hVo : IsOpen (X := PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen
  have hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg)) := hpV
  obtain ⟨W, ⟨f, rfl⟩, h1, h2⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open
    (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo
  exact ⟨f, h1, h2⟩

/- English proof (translation)
Establish `hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg))`. Rewrite using `[← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`.

Conclude with `⟨x, rfl⟩`. Conclude with `hfV (hg h1)`. Conclude with `⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩`.
-/
theorem exists_factor_away {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (f g : Rg)
    (hfV : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg)))
    (hg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ uV : Sp (Localization.Away g) ⟶ V.toScheme, uV ≫ V.ι = spMap (algebraMap Rg (Localization.Away g)) := by
  have hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨x, rfl⟩
    exact hfV (hg h1)
  exact ⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩

/- English proof (translation)
Establish `hAgw : φ ≫ A.hom = Ag.hom ≫ u` using `hφ.1.w`. Establish `hw : ((snd (overRes (T` using `baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom = ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by`. Establish `e` using `(GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w`. Simplify using `only [Category.assoc, hAgw]`. Rewrite using `[← Category.assoc, e]`.

Simplify using `[overRes, baseOver, huV]`. Take `⟨H, hH1, hH2⟩ : ∃ H : (overRes (T` from `baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left, H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧ H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left …`. Establish `hc : ∀ _ : Fin 1, (snd (overRes (T` using `baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left := fun _ => hH1.symm`. Use `⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left) (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩` and prove the remaining obligations. Introduce `R _ t b' hb'`.

Take `⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T` from `baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩`. Use `choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)`. Establish `hB` using `hb R t' b'' hb''`. Establish `hxy : (t ≫ (overRes (T` using `baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by`. Rewrite using `[ht']`.

Simplify using `[overRes, baseOver, huV]`. Establish `hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom`. Establish `e` using `(GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w`. Simplify using `only [Category.assoc, hAgw]`. Rewrite using `[← Category.assoc, e]`.

Simplify using `[baseAt, overRes, baseOver, ht', huV]`. Take `⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left, h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧ h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left` from `⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩`. Establish `hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left` using `fun _ => hh1.symm`. Use `GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2` and prove the remaining obligations. Establish `hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left`.

Apply `(GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]`. Establish `e1` using `GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)`. Establish `e2` using `GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Category.assoc, hH2, Category.assoc]`. Use `_ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by`. Rewrite using `[e1]`. Apply the tactic sequence `try simp [homAt]`. Use `_ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by`.

Rewrite using `[Category.assoc, e2, reassoc_of% hh2, ht']`. Apply the tactic sequence `try simp [homAt]`. Introduce `i`. Apply `GlobalTheory.SecTwist.sec_ext_loc` to reduce the goal to its premises. Introduce `y`.

Take `⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j` from `exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y`. Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Establish `hj1` using `chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj`. Establish `hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit)`. Use `(chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left) (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj` as an intermediate fact.

Conclude with `this`. Establish `lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) = gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T` using `baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit)) ((b i).f (fun k => j k PUnit.unit)) := by`. Rewrite using `[hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]`. Conclude with `GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left) (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1`. Establish `rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left) (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) = gs (h ≫ (homAt t' ▷ A).left) y (( …` using `baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit)) ((b i).f (fun k => j k PUnit.unit)) := by`.

Establish `e1` using `GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left) (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj`. Rewrite `e1` using `[Category.id_comp]`. Use `e1.trans ?_` and prove the remaining obligations. Use `erw [hb'' i (fun k => j k PUnit.unit)]`. Conclude with `GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _`.

Rewrite using `[lhs, rhs, hcomp]`.
-/
theorem secBasis_of_factor {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (k : ℕ) (V : (Sp Rg).Opens) (m : ℕ)
    (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤)
    {S' : Scheme.{0}} (u : S' ⟶ Sp Rg) (uV : S' ⟶ V.toScheme) (huV : uV ≫ V.ι = u)
    (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (hφ : IsGrpPullback Ag A u φ) :
    ∃ (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver S') ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S') ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤ := by
  have hAgw : φ ≫ A.hom = Ag.hom ≫ u := hφ.1.w
  have hw : ((snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom =
      ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [overRes, baseOver, huV]
  obtain ⟨H, hH1, hH2⟩ : ∃ H : (overRes (T := baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left,
      H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧
      H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw⟩
  have hc : ∀ _ : Fin 1, (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left :=
    fun _ => hH1.symm
  refine ⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
    (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩
  intro R _ t b' hb'
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩
  choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)
  have hB := hb R t' b'' hb''
  have hxy : (t ≫ (overRes (T := baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    rw [ht']
    simp [overRes, baseOver, huV]
  have hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [baseAt, overRes, baseOver, ht', huV]
  obtain ⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left,
      h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧
      h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩
  have hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left := fun _ => hh1.symm
  refine GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2
  have hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left := by
    apply (GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext
    · rw [Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]
    · have e1 := GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)
      have e2 := GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')
      calc ((homAt t ▷ Ag).left ≫ H) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left
            = ((homAt t ▷ Ag).left ≫ (fst (overRes (T := baseOver S') ⊤) Ag).left) ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [Category.assoc, hH2, Category.assoc]
        _ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [e1]
              try simp [homAt]
        _ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by
              rw [Category.assoc, e2, reassoc_of% hh2, ht']
              try simp [homAt]
  intro i
  apply GlobalTheory.SecTwist.sec_ext_loc
  intro y
  obtain ⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j :=
    exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y
  refine ⟨j, hj, ?_⟩
  have hj1 := chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj
  have hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit) := by
    have := (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
      (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj
    exact this
  have lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) =
      gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    rw [hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]
    exact GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
      (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1
  have rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j)
      ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) =
      gs (h ≫ (homAt t' ▷ A).left) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    have e1 := GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj
    rw [Category.id_comp] at e1
    refine e1.trans ?_
    erw [hb'' i (fun k => j k PUnit.unit)]
    exact GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _
  rw [lhs, rhs, hcomp]

/- English proof (translation)
Introduce `Rg _ _ A _ _ L hAb hL hRig hAmp k hk p`. Take `⟨V, hpV, m, b, hb⟩` from `GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p`. Establish `hx` using `exists_basicOpen_le (Rg := Rg) V p hpV`. Use `⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩` and prove the remaining obligations. Establish `hu` using `exists_factor_away V _ g hx.choose_spec.2 hg`.

Conclude with `secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ`.
-/
theorem exists_basicOpen_secBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  intro Rg _ _ A _ _ L hAb hL hRig hAmp k hk p
  obtain ⟨V, hpV, m, b, hb⟩ := GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p
  have hx := exists_basicOpen_le (Rg := Rg) V p hpV
  refine ⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩
  have hu := exists_factor_away V _ g hx.choose_spec.2 hg
  exact secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ

end GlobalTheory.HomFixLocBasis
