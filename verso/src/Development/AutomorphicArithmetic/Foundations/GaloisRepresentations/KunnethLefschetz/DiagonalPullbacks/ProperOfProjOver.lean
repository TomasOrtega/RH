import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsProjOver PSpace Sp)

/- English proof (translation)
Take `⟨N, i, hi, rfl⟩` from `h`. Use `haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N`. Use `infer_instance`.
-/
private theorem proper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} (h : IsProjOver p) :
    IsProper p := by
  obtain ⟨N, i, hi, rfl⟩ := h
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

/- English proof (translation)
The claim follows from `GlobalTheory.ProjSpace.isProjOver_pullback_snd (OK l K).subtype h.1.1`.
-/
private theorem gen_proj {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K)
    (h : M.Sm) : IsProjOver M.q :=
  GlobalTheory.ProjSpace.isProjOver_pullback_snd (OK l K).subtype h.1.1

/- English proof (translation)
The claim follows from `proper_of_projOver (gen_proj M h)`.
-/
private theorem gen_proper {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K)
    (h : M.Sm) : IsProper M.q :=
  proper_of_projOver (gen_proj M h)

/- English proof (translation)
Introduce `l _ K`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `M d hM hd haveI := gen_proper M hM`. Establish `stab` using `smoothOfRelativeDimension_isStableUnderBaseChange (n := d)`. Establish `hq : SmoothOfRelativeDimension d M.q` using `stab.of_isPullback (IsPullback.of_hasPullback _ _) hd`.

Use `⟨⟨inferInstance, stab.of_isPullback (IsPullback.of_hasPullback _ _) hq⟩, ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap (↥K) (PadicAlgCl l)) (gen_proj M hM)`. Introduce `M N u hu hM hN haveI := gen_proper M hM haveI := gen_proper N hN haveI : IsProper (Model.genMap u hu ≫ N.q) := by`. Rewrite using `[Model.genMap_q u hu]`. Use `infer_instance`.

Conclude with `IsProper.of_comp _ N.q`. Introduce `M P p₁ p₂ h₁ h₂ H set j := Spec.map (CommRingCat.ofHom (OK l K).subtype)`. Establish `sqM : IsPullback (pullback.fst M.p j) M.q M.p j` using `IsPullback.of_hasPullback _ _`. Establish `sqP : IsPullback (pullback.fst P.p j) P.q P.p j` using `IsPullback.of_hasPullback _ _`. Establish `hfst : ∀ (u : P.X ⟶ M.X) (hu : u ≫ M.p = P.p), Model.genMap u hu ≫ pullback.fst M.p j = pullback.fst P.p j ≫ u`.

Introduce `u hu`. Unfold `Model.genMap`. Conclude with `pullback.lift_fst _ _ _`. Establish `side : ∀ (u : P.X ⟶ M.X) (hu : u ≫ M.p = P.p), IsPullback (Model.genMap u hu) (pullback.fst P.p j) (pullback.fst M.p j) u`. Introduce `u hu`.

Use `IsPullback.of_right ?_ (hfst u hu) sqM.flip` and prove the remaining obligations. Rewrite using `[Model.genMap_q u hu, hu]`. Conclude with `sqP.flip`. Establish `big` using `(side p₁ h₁).paste_vert H`. Use `IsPullback.of_bot ?_ ?_ sqM.flip` and prove the remaining obligations.

Rewrite using `[hfst p₂ h₂, ← sqM.w]`. Conclude with `big`. Rewrite using `[Model.genMap_q, Model.genMap_q]`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.Di.geoM_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.GeoM := by
  intro l _ K
  refine ⟨?_, ?_, ?_⟩
  · intro M d hM hd
    haveI := gen_proper M hM
    have stab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    have hq : SmoothOfRelativeDimension d M.q :=
      stab.of_isPullback (IsPullback.of_hasPullback _ _) hd
    refine ⟨⟨inferInstance, stab.of_isPullback (IsPullback.of_hasPullback _ _) hq⟩, ?_⟩
    exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap (↥K) (PadicAlgCl l)) (gen_proj M hM)
  · intro M N u hu hM hN
    haveI := gen_proper M hM
    haveI := gen_proper N hN
    haveI : IsProper (Model.genMap u hu ≫ N.q) := by
      rw [Model.genMap_q u hu]
      infer_instance
    exact IsProper.of_comp _ N.q
  · intro M P p₁ p₂ h₁ h₂ H
    set j := Spec.map (CommRingCat.ofHom (OK l K).subtype)
    have sqM : IsPullback (pullback.fst M.p j) M.q M.p j := IsPullback.of_hasPullback _ _
    have sqP : IsPullback (pullback.fst P.p j) P.q P.p j := IsPullback.of_hasPullback _ _
    have hfst : ∀ (u : P.X ⟶ M.X) (hu : u ≫ M.p = P.p),
        Model.genMap u hu ≫ pullback.fst M.p j = pullback.fst P.p j ≫ u := by
      intro u hu
      unfold Model.genMap
      exact pullback.lift_fst _ _ _
    have side : ∀ (u : P.X ⟶ M.X) (hu : u ≫ M.p = P.p),
        IsPullback (Model.genMap u hu) (pullback.fst P.p j) (pullback.fst M.p j) u := by
      intro u hu
      refine IsPullback.of_right ?_ (hfst u hu) sqM.flip
      rw [Model.genMap_q u hu, hu]
      exact sqP.flip
    have big := (side p₁ h₁).paste_vert H
    refine IsPullback.of_bot ?_ ?_ sqM.flip
    · rw [hfst p₂ h₂, ← sqM.w]
      exact big
    · rw [Model.genMap_q, Model.genMap_q]
