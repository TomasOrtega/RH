import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesUniqueOpenChartStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTriangularFrameRingOverTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestRingLocalizationAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFrameTestRingStatement
import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CommonEigenvectorsFlatBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.LamLoc

/- English proof (translation)
Introduce `hS E _ _ _ H Dw l Xo c p A j y₀ π X s u hj hU`. Take `⟨B, q, Y, r, hYd, hYz, hY⟩` from `GlobalTheory.T.exists_triangularFrameRing_over_testRing c.F (E →+* ℂ) (fun τ => Dw.mult τ) A`. Take `⟨uB, huB⟩` from `GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A.R B.R q u`. Take `⟨uB', huB', -⟩` from `GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c B.R uB Y r fun τ => lowerTri_isUnit_det _ (hYz τ) (hYd τ)`. Establish `hux : u.x = spMap π.toRingHom ≫ y₀.x`.

Take `⟨-, u₀, h₀, h₁⟩` from `hU`. Conclude with `h₁.1.trans h₀.1`. Establish `hx' : uB'.x = spMap (q.comp π).toRingHom ≫ y₀.x`. Rewrite using `[huB'.1, huB.1, hux, spMap_algHom_comp, Category.assoc]`. Take `⟨q', ⟨-, hq'⟩, -⟩` from `GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c p.R A.R y₀ π X s u hU B.R uB' (q.comp π) hx'`.

Use `⟨B, uB, uB', fun k => match k with` and prove the remaining obligations. Consider the case `none => r`. Consider the case `some ⟨τ, i⟩ => (hYd τ i).unit, q, q', huB, hq',`. Use the proof step `(frBor_iff_frChg uB uB' _).2 ⟨Y, hYz, fun τ i => (hYd τ i).unit_spec.symm, huB'⟩, ?_⟩`. Introduce `T _ _ a a' z z' t hz hz' hb`.

Take `⟨g, hgz, hgd, hgc⟩` from `(frBor_iff_frChg z z' t).1 hb`. Take `⟨b, ⟨hb1, hb2, hb3⟩, -⟩` from `hY T a g (t none) (fun τ i => by rw [hgd]; exact Units.isUnit _) hgz`. Establish `h1 : FrMap b uB z` using `frMap_cancel (Xo := Xo) (c := c) _ _ _ q b u uB z huB (by rw [hb1]; exact hz)`. Establish `h2 : FrMap b uB' z'`. Use `(GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c B.R T b uB uB' z z' Y r huB' h1).2 ?_` and prove the remaining obligations.

Rewrite using `[hb3, funext hb2]`. Conclude with `hgc`. Establish `h3 : FrMap (b.comp q') u z'` using `frMap_trans (Xo := Xo) (c := c) _ _ _ q' b u uB' z' hq' h2`. Use `⟨b, hb1, GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hU T _ _ z' h3 hz', ?_⟩` and prove the remaining obligations. Introduce and unpack `(_ | ⟨τ, i⟩)`.

Conclude with `hb3`. Use `show b (Y τ i i) = _`. Rewrite using `[← hgd, ← hb2 τ]`. Both sides reduce to the same expression.
-/
theorem univFrame_borelPairs : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  intro hS E _ _ _ H Dw l Xo c p A j y₀ π X s u hj hU
  obtain ⟨B, q, Y, r, hYd, hYz, hY⟩ := GlobalTheory.T.exists_triangularFrameRing_over_testRing c.F (E →+* ℂ) (fun τ => Dw.mult τ) A
  obtain ⟨uB, huB⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A.R B.R q u
  obtain ⟨uB', huB', -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c B.R uB Y r
    fun τ => lowerTri_isUnit_det _ (hYz τ) (hYd τ)
  have hux : u.x = spMap π.toRingHom ≫ y₀.x := by
    obtain ⟨-, u₀, h₀, h₁⟩ := hU
    exact h₁.1.trans h₀.1
  have hx' : uB'.x = spMap (q.comp π).toRingHom ≫ y₀.x := by
    rw [huB'.1, huB.1, hux, spMap_algHom_comp, Category.assoc]
  obtain ⟨q', ⟨-, hq'⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c p.R A.R y₀ π X s u hU B.R uB' (q.comp π) hx'
  refine ⟨B, uB, uB', fun k => match k with
    | none => r
    | some ⟨τ, i⟩ => (hYd τ i).unit, q, q', huB, hq',
    (frBor_iff_frChg uB uB' _).2 ⟨Y, hYz, fun τ i => (hYd τ i).unit_spec.symm, huB'⟩, ?_⟩
  intro T _ _ a a' z z' t hz hz' hb
  obtain ⟨g, hgz, hgd, hgc⟩ := (frBor_iff_frChg z z' t).1 hb
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, -⟩ := hY T a g (t none)
    (fun τ i => by rw [hgd]; exact Units.isUnit _) hgz
  have h1 : FrMap b uB z :=
    frMap_cancel (Xo := Xo) (c := c) _ _ _ q b u uB z huB (by rw [hb1]; exact hz)
  have h2 : FrMap b uB' z' := by
    refine (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c B.R T b uB uB' z z' Y r huB' h1).2 ?_
    rw [hb3, funext hb2]
    exact hgc
  have h3 : FrMap (b.comp q') u z' := frMap_trans (Xo := Xo) (c := c) _ _ _ q' b u uB' z' hq' h2
  refine ⟨b, hb1, GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hU T _ _ z' h3 hz', ?_⟩
  rintro (_ | ⟨τ, i⟩)
  · exact hb3
  · show b (Y τ i i) = _
    rw [← hgd, ← hb2 τ]
    rfl

end GlobalTheory.LamLoc

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.LamLoc

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Use `⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩` and prove the remaining obligations. Rewrite using `[w.x_over, spMap_comp_ring]`. Both sides reduce to the same expression.
-/
theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

/- English proof (translation)
Take `⟨g, hg, hT⟩` from `openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp`. Use `⟨g, hg, fun T _ _ lam hl => ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `hT T lam hl`. Take `⟨z, hz⟩` from `GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w`. Establish `hx : z.x = spMap ψ.toRingHom ≫ y₀.x`.

Rewrite using `[hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]`. Take `⟨a, ⟨_, ha⟩, _⟩` from `GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx`. Conclude with `⟨z, a, hz, ha⟩`.
-/
theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

/- English proof (translation)
Take `⟨g, hg, hT⟩` from `ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp`. Take `⟨z, a, hz, ha⟩` from `hT (Localization.AtPrime m) (locM c.F m) (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))`. Use `⟨a, ⟨z, hz, ha⟩, ?_⟩` and prove the remaining obligations. Introduce `p φ y hy`. Take `⟨yF, k1, k2⟩` from `ChartCover.exists_lift y`.

Establish `e : spMap φ.toRingHom ≫ yF = xF`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, k1, h1, hy.1]`. Rewrite using `[Category.assoc, k2, h2, spMap_comp_ring]`. Use `congr 1`.

Conclude with `φ.comp_algebraMap`. Establish `hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j`. Rewrite `hp` using `[← e]`. Conclude with `hp`. Take `⟨g', hg', hT'⟩` from `ChartCover.near hS hj hu y yF k1 k2 _ hq`.

Take `⟨p', lam, hl, hlam⟩` from `GlobalTheory.testRing_localizationAway c.F p g'`. Take `⟨z', a', hz', ha'⟩` from `hT' p'.R lam hl`. Conclude with `⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩`.
-/
theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

/- English proof (translation)
Introduce `hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm`. Take `⟨xF, h1, h2⟩` from `ChartCover.exists_lift w`. Take `⟨p, j, y₀, hj, hp⟩` from `GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))`. Take `⟨A, π, X, s, u, hu⟩` from `GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀`. Take `⟨cw, hc, hl⟩` from `ChartCover.cls_loc hS hj hu w xF h1 h2 m hp`.

Take `⟨cw', hc', hl'⟩` from `ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp`. Conclude with `⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu, GlobalTheory.LamLoc.univFrame_borelPairs hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩`.
-/
theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    GlobalTheory.LamLoc.univFrame_borelPairs hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

end GlobalTheory.LamLoc

end

section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

/- English proof (translation)
Introduce `f hf t y y' hb`. Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Establish `hall` using `GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c`. Conclude with `wtAll_of_borChart (borChartF_of_cover (GlobalTheory.LamLoc.chartCoverF_of_secBaseChange hS E H Dw l Xo c)) (ex Dw a n) hf.1 hf.2 S t y y' (hall S y) (hall S y') hb`.
-/
theorem GlobalTheory.LamLoc.evR_frBor (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∀ f ∈ sec Xo c a n, ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
      evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  intro f hf t y y' hb
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hall := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact wtAll_of_borChart (borChartF_of_cover (GlobalTheory.LamLoc.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
    (ex Dw a n) hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

end

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LamLoc.AlgLawsCompare

open NumberField IsDedekindDomain IsLocalRing AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

section Valuations

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

end Valuations

end GlobalTheory.LamLoc.AlgLawsCompare

end

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.LamLoc.IntLie

section Pull

variable {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
  {φ : G'.left ⟶ G.left}

/- English proof (translation)
Set `e0 : Over.mk (T.hom ≫ f) ⟶ G` to `Over.homMk ((1 : T ⟶ G').left ≫ φ) (by show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f`. Rewrite using `[Category.assoc, h.1.w, ← Category.assoc, Over.w])`. Establish `h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ` using `h.2 T 1 1 e0 e0 rfl rfl`. Rewrite `h1` using `[_root_.mul_one]`. Establish `h2 : e0 * e0 = e0` using `Over.OverMorphism.ext h1`.

Establish `h3 : e0 = 1` using `mul_eq_left.1 h2`. Rewrite using `[← h3]`. Both sides reduce to the same expression.
-/
theorem one_push₀ (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

/- English proof (translation)
Set `δ : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk g hg`. Rewrite using `[← one_push₀ h T', ← MonObj.comp_one δ]`. Both sides reduce to the same expression.
-/
theorem one_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = g ≫ (1 : T ⟶ G).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← one_push₀ h T', ← MonObj.comp_one δ]
  rfl

/- English proof (translation)
Set `δ : Over.mk (T'.hom ≫ f) ⟶ T` to `Over.homMk g hg`. Rewrite using `[← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]`. Both sides reduce to the same expression.
-/
theorem mul_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) (a b : T' ⟶ G') (a₀ b₀ : T ⟶ G) (ha : a.left ≫ φ = g ≫ a₀.left)
    (hb : b.left ≫ φ = g ≫ b₀.left) : (a * b).left ≫ φ = g ≫ (a₀ * b₀).left := by
  let δ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g hg
  rw [← h.2 T' a b (δ ≫ a₀) (δ ≫ b₀) ha.symm hb.symm, ← MonObj.comp_mul]
  rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using one_push h T' T g hg`. Consider the case `succ m ih`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]`. Conclude with `mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)`.
-/
theorem prod_push (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T'.left ⟶ T.left)
    (hg : g ≫ T.hom = T'.hom ≫ f) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a j).left ≫ φ = g ≫ (a₀ j).left) :
    ((List.ofFn a).prod).left ≫ φ = g ≫ ((List.ofFn a₀).prod).left := by
  induction m with
  | zero => simpa using one_push h T' T g hg
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_push h T' T g hg _ _ _ _ (ha 0) (ih _ _ fun j => ha j.succ)

end Pull

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite `e`, the goal using `[← Spec.map_preimage g, ← Spec.map_preimage h]`. Simplify using `only [spMap, ← Spec.map_comp] at e`. Establish `e1` using `Spec.map_injective e`. Use `congr 1`. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `IsLocalization.ringHom_ext (nonZeroDivisors V)` to reduce the goal to its premises. Conclude with `congrArg CommRingCat.Hom.hom e1`.
-/
theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [dualMap, epsMul, _root_.mul_comm]`.
-/
theorem dualMap_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.LamLoc.IntLie

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.TieCalc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

end GlobalTheory.LamLoc.TieCalc

end

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamLoc.LocLie

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
The claim follows from `(isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) _ _).1 h`.
-/
theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) :
    (combT x (fun j => ovT (t := Xo.univ.t) (hv j)) a).left = w :=
  (isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) _ _).1 h

/- English proof (translation)
Take `⟨ub, htan, heig, hbas, hlift⟩` from `h`. Set `Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G)` to `fun τ j => kapSat ≫ ub τ j`. Establish `hUb0 : ∀ τ j, smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1` using `fun τ j => smT_zero_kap _ (htan τ j)`. Establish `hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) → Ub τ j ≫ G.act.act a = smT (𝟙 (Sp T.V)) z (Ub τ j)` using `fun τ j => (isEigV_kapI_iff io G τ _).1 (by rw [kapI_kap_assoc]; exact heig τ j)`. Use `⟨fun τ i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `τ i`. Conclude with `isTan_kapI _ (combT_tan _ _ (hUb0 τ) _)`. Introduce `τ i`. Use `(isEigV_kapI_iff io G τ _).2 fun a z hz => ?_` and prove the remaining obligations. Use `G.act.hom a` as an intermediate fact.

Conclude with `combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _`. Introduce `τ w hw he`. Establish `h1 : ∃! a : Fin (Dw.mult τ) → T.V, kapSat ≫ w = combT (𝟙 (Sp T.V)) (Ub τ) a`. Take `⟨a, ha, hu⟩` from `hbas τ w hw he`. Use `⟨a, (isComb_iff _ _ _).1 (by rw [kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩` and prove the remaining obligations.

Establish `h2` using `(isComb_iff (ub τ) b (kapSat ≫ w)).2 hb`. Rewrite `h2` using `[kapI_kap_assoc]`. Conclude with `h2`. Take `⟨a, ha, hu⟩` from `reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1`. Establish `e : (fun i => kapSat ≫ (kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) = fun i => combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)` using `funext fun i => kap_kapI_assoc _`.

Use `⟨a, ?_, fun b hb => hu b ?_⟩` and prove the remaining obligations. Establish `h2` using `(isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kapSat ≫ w)).2 (by rw [e]; exact ha)`. Rewrite `h2` using `[kapI_kap_assoc]`. Conclude with `h2`. Establish `h2` using `(isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kapSat ≫ w)).1 (by rw [kapI_kap_assoc]; exact hb)`.

Rewrite `h2` using `[e]`. Conclude with `h2`. Introduce `τ i choose u' hu1 hu2 using hlift τ`. Establish `hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr)`. Rewrite using `[spMap_comp', spMap_comp']`.

Use `show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _`. Rewrite using `[dualMap_comp_alg]`. Establish `hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))`. Introduce `j`. Apply `spMap_frac_cancel (V := T.V)` to reduce the goal to its premises.

Rewrite using `[Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]`. Conclude with `hδ`. Set `T' : Over (Sp T.Fr)` to `Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))`. Set `cf : Fin (Dw.mult τ) → T.Fr` to `fun j => algebraMap T.V T.Fr (k τ j i)`. Set `Y : Fin (Dw.mult τ) → (T' ⟶ t'.G)` to `fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))`.

Rewrite using `[Category.assoc, hov, spMap_comp', epsMul_comp_alg])`. Use `⟨(∏ j, Y j).left, ?_, ?_⟩` and prove the remaining obligations. Establish `hA` using `grpPull_prod m1.cart T' Finset.univ Y (fun j => smT x (cf j) (ovT (t := Xo.univ.t) (hu τ j))) (fun j => by show spMap (epsMul (cf j)) ≫ u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ`. Rewrite using `[Category.assoc, hu1])`. Conclude with `hA.symm`.

Set `δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V` to `Over.homMk (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) hδ`. Establish `hB` using `grpPull_prod m2.cart T' Finset.univ Y (fun j => δ ≫ kapI ≫ smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by`. Simplify using `only [Over.comp_left, δ, kapI, Formalism.L2.Pj.kapSat, Ub, smT_left, Over.homMk_left, Category.id_comp, Y, Category.assoc]`. Rewrite using `[hu2 j, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul])`. Rewrite using `[← hB, ← comp_prodT, ← comp_prodT]`.

Both sides reduce to the same expression.
-/
theorem lieInt_change (T : CDVR) (io : c.F →+* T.Fr) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ j, IsTanAt x (u τ j)) (h : LieInt T io m1 m2 u)
    (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (hk : ∀ τ, IsUnit (k τ).det) :
    LieInt T io m1 m2 (fun τ i => (combT x (fun j => ovT (t := Xo.univ.t) (hu τ j))
      (fun j => algebraMap T.V T.Fr (k τ j i))).left) := by
  obtain ⟨ub, htan, heig, hbas, hlift⟩ := h
  let Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G) := fun τ j => kapSat ≫ ub τ j
  have hUb0 : ∀ τ j, smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1 := fun τ j => smT_zero_kap _ (htan τ j)
  have hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) →
      Ub τ j ≫ G.act.act a = smT (𝟙 (Sp T.V)) z (Ub τ j) := fun τ j =>
    (isEigV_kapI_iff io G τ _).1 (by rw [kapI_kap_assoc]; exact heig τ j)
  refine ⟨fun τ i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩
  · intro τ i
    exact isTan_kapI _ (combT_tan _ _ (hUb0 τ) _)
  · intro τ i
    refine (isEigV_kapI_iff io G τ _).2 fun a z hz => ?_
    have := G.act.hom a
    exact combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _
  · intro τ w hw he
    have h1 : ∃! a : Fin (Dw.mult τ) → T.V, kapSat ≫ w = combT (𝟙 (Sp T.V)) (Ub τ) a := by
      obtain ⟨a, ha, hu⟩ := hbas τ w hw he
      refine ⟨a, (isComb_iff _ _ _).1 (by rw [kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩
      have h2 := (isComb_iff (ub τ) b (kapSat ≫ w)).2 hb
      rw [kapI_kap_assoc] at h2
      exact h2
    obtain ⟨a, ha, hu⟩ := reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1
    have e : (fun i => kapSat ≫ (kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) =
        fun i => combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i) := funext fun i => kap_kapI_assoc _
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kapSat ≫ w)).2
        (by rw [e]; exact ha)
      rw [kapI_kap_assoc] at h2
      exact h2
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kapSat ≫ w)).1
        (by rw [kapI_kap_assoc]; exact hb)
      rw [e] at h2
      exact h2
  · intro τ i
    choose u' hu1 hu2 using hlift τ
    have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [spMap_comp', spMap_comp']
      show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [dualMap_comp_alg]
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]
      exact hδ
    let T' : Over (Sp T.Fr) := Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))
    let cf : Fin (Dw.mult τ) → T.Fr := fun j => algebraMap T.V T.Fr (k τ j i)
    let Y : Fin (Dw.mult τ) → (T' ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by
      show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))
      rw [Category.assoc, hov, spMap_comp', epsMul_comp_alg])
    refine ⟨(∏ j, Y j).left, ?_, ?_⟩
    · have hA := grpPull_prod m1.cart T' Finset.univ Y
        (fun j => smT x (cf j) (ovT (t := Xo.univ.t) (hu τ j))) (fun j => by
          show spMap (epsMul (cf j)) ≫ u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ
          rw [Category.assoc, hu1])
      exact hA.symm
    · let δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V :=
        Over.homMk (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) hδ
      have hB := grpPull_prod m2.cart T' Finset.univ Y
        (fun j => δ ≫ kapI ≫ smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by
          simp only [Over.comp_left, δ, kapI, Formalism.L2.Pj.kapSat, Ub, smT_left, Over.homMk_left, Category.id_comp, Y,
            Category.assoc]
          rw [hu2 j, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul])
      rw [← hB, ← comp_prodT, ← comp_prodT]
      rfl

end GlobalTheory.LamLoc.LocLie

end

end

section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.LocSec

end GlobalTheory.LamLoc.LocSec

end

end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.KeyVal

end GlobalTheory.LamLoc.KeyVal

end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.LieIntBC

open Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg tvec_tmap fB IsUnivChart sp JetR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp]`. Use `congr 1`. Apply the tactic sequence `ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.LamLoc.LieIntBC

namespace GlobalTheory.LamLoc

open LieIntBC Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec tvec_tmap)

end GlobalTheory.LamLoc

end

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

noncomputable section

namespace GlobalTheory.LamLoc

end GlobalTheory.LamLoc

end

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.LetterInt

open GlobalTheory.LamLoc.IntLie

/- English proof (translation)
Set `δ : Over.mk (g ≫ T'.hom) ⟶ T'` to `Over.homMk g rfl`. Establish `h1` using `prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _) ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀ (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))`. Establish `h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod`. Introduce `m a`. Proceed by induction on `m with`.

Consider the case `zero => simp [MonObj.comp_one]`. Consider the case `succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]`. Rewrite `h1` using `[h2]`. Conclude with `((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)`.
-/
theorem prod_pull {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T.left ⟶ T'.left)
    (hg : g ≫ T'.hom ≫ f = T.hom) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a₀ j).left = g ≫ (a j).left ≫ φ) :
    ((List.ofFn a₀).prod).left = g ≫ ((List.ofFn a).prod).left ≫ φ := by
  let δ : Over.mk (g ≫ T'.hom) ⟶ T' := Over.homMk g rfl
  have h1 := prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _)
    ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀
    (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))
  have h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod := by
    intro m a
    induction m with
    | zero => simp [MonObj.comp_one]
    | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]
  rw [h2] at h1
  exact ((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)

/- English proof (translation)
Take `⟨u₁, hu₁, rfl⟩` from `hw₁`. Take `⟨u₂, hu₂, rfl⟩` from `hw₂`. Set `T : Over X` to `Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)`. Establish `e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, IntLie.dualMap_alg]`.

Establish `e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, IntLie.dualMap_alg]`. Set `Z : Fin m → (T ⟶ B)` to `fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁`. Rewrite using `[Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]`. Conclude with `e₁)`.

Establish `k₁` using `prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)`. Establish `k₂` using `prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _`. Establish `a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α)`. Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Both sides reduce to the same expression.

Establish `a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β)`. Rewrite using `[spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]`. Both sides reduce to the same expression. Rewrite using `[hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])`. Conclude with `k₁.symm.trans k₂`.
-/
theorem comb_match {V K F : Type} [CommRing V] [CommRing K] [CommRing F] {X : Scheme.{0}} {B : Over X} [GrpObj B]
    {G₁ : Over (Sp V)} [GrpObj G₁] {G₂ : Over (Sp K)} [GrpObj G₂] {f₁ : Sp V ⟶ X} {f₂ : Sp K ⟶ X}
    {φ₁ : G₁.left ⟶ B.left} {φ₂ : G₂.left ⟶ B.left} (h₁ : IsGrpPullback G₁ B f₁ φ₁) (h₂ : IsGrpPullback G₂ B f₂ φ₂)
    (α : V →+* F) (β : K →+* F) (hf : spMap α ≫ f₁ = spMap β ≫ f₂) {m : ℕ} {v₁ : Fin m → (epsR V ⟶ G₁)}
    {v₂ : Fin m → (epsR K ⟶ G₂)}
    (hv : ∀ i, spMap (dualMap α) ≫ (v₁ i).left ≫ φ₁ = spMap (dualMap β) ≫ (v₂ i).left ≫ φ₂)
    {c₁ : Fin m → V} {c₂ : Fin m → K} (hc : ∀ i, α (c₁ i) = β (c₂ i)) {w₁ : epsR V ⟶ G₁} {w₂ : epsR K ⟶ G₂}
    (hw₁ : IsLieComb c₁ v₁ w₁) (hw₂ : IsLieComb c₂ v₂ w₂) :
    spMap (dualMap α) ≫ w₁.left ≫ φ₁ = spMap (dualMap β) ≫ w₂.left ≫ φ₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := hw₁
  obtain ⟨u₂, hu₂, rfl⟩ := hw₂
  let T : Over X := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)
  have e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, IntLie.dualMap_alg]
  have e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, IntLie.dualMap_alg]
  let Z : Fin m → (T ⟶ B) := fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by
    show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]
    exact e₁)
  have k₁ := prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)
  have k₂ := prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by
    show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _
    have a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    have a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    rw [hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])
  exact k₁.symm.trans k₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.LamLoc.LetterInt

end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.LocGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

end GlobalTheory.LamLoc.LocGen

end

end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamLoc.LocClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.LamLoc.LocClause

end
