import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsQProjOverOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

/- English proof (translation)
Introduce `hG l _ K O _ _ φ Y W p d hs hp c _ _`. Use `haveI : SmoothOfRelativeDimension d p := hs`. Use `haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance`. Establish `hcs : SmoothOfRelativeDimension d (c ≫ p)`. Establish `h : SmoothOfRelativeDimension (0 + d) (c ≫ p)` using `inferInstance`.

Rewrite `h` using `[Nat.zero_add]`. Then use the resulting hypothesis. Establish `hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ)))` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs`. Establish `hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p)` using `GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)`. Use `haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp`. Establish `hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p)` using `GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance`.

Establish `hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ)))` using `GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp`. Use `haveI : FiniteDimensional ℚ_[l] K.1 := K.2`. Establish `hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ)))` using `SmoothOfRelativeDimension.smooth d _`. Conclude with `⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩`.
-/
theorem UpperTheory.Gal.G3.jModBc :
    UpperTheory.Gal.Seam.GoodOf → ModBc := by
  intro hG l _ K O _ _ φ Y W p d hs hp c _ _
  haveI : SmoothOfRelativeDimension d p := hs
  haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance
  have hcs : SmoothOfRelativeDimension d (c ≫ p) := by
    have h : SmoothOfRelativeDimension (0 + d) (c ≫ p) := inferInstance
    rwa [Nat.zero_add] at h
  have hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs
  have hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)
  haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  have hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p) :=
    GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance
  have hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    SmoothOfRelativeDimension.smooth d _
  exact ⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩
