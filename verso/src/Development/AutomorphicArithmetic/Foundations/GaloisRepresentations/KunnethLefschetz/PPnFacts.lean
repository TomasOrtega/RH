import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.LProperPf
import Development.EtaleCohomology.EtaleTrace.PNIntegralPf
import Development.EtaleCohomology.EtaleTrace.LSmoothPf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.PnF
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

private def chartE (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) :
    Chart k i ≃+* MvPolynomial (Fin N) k :=
  (chartEquiv k i).trans (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm).toRingEquiv

/- English proof (translation)
Establish `h : HomogeneousLocalization.fromZeroRingHom (grading k N) _ (algebraMap k (grading k N 0) a) = polyToChart k i (MvPolynomial.C a)`. Simplify using `[polyToChart]`. Rewrite using `[h]`. Establish `h2 : chartToPoly k i (polyToChart k i (MvPolynomial.C a)) = MvPolynomial.C a`. Rewrite using `[← RingHom.comp_apply, chartToPoly_polyToChart]`.

Both sides reduce to the same expression. Simplify using `only [chartE, RingEquiv.trans_apply]`. Express the relevant statement in the definitionally equal form `(MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm) (chartToPoly k i (polyToChart k i (MvPolynomial.C a))) = _`. Rewrite using `[h2]`. Simplify using the standard rewrite rules.
-/
private theorem chartE_C (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) (a : k) :
    chartE k N i (HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a)) = MvPolynomial.C a := by
  have h : HomogeneousLocalization.fromZeroRingHom (grading k N) _
      (algebraMap k (grading k N 0) a) = polyToChart k i (MvPolynomial.C a) := by
    simp [polyToChart]
  rw [h]
  have h2 : chartToPoly k i (polyToChart k i (MvPolynomial.C a)) = MvPolynomial.C a := by
    rw [← RingHom.comp_apply, chartToPoly_polyToChart]
    rfl
  simp only [chartE, RingEquiv.trans_apply]
  change (MvPolynomial.renameEquiv k (finSuccAboveEquiv i).symm)
    (chartToPoly k i (polyToChart k i (MvPolynomial.C a))) = _
  rw [h2]
  simp

/- English proof (translation)
Introduce `k _ N i`. Set `e` to `chartE k N i`. Set `ι` to `Proj.awayι (grading k N) (MvPolynomial.X i) (X_mem i) one_pos`. Establish `hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom))`. Establish `: IsIso (CommRingCat.ofHom e.toRingHom)` using `(RingEquiv.toCommRingCatIso e).isIso_hom`.

Use `infer_instance`. Use `⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ ι, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [PNto, Category.assoc]`. Rewrite using `[Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `a`. Conclude with `congrArg (MvPolynomial.coeff _) (chartE_C k N i a)`. Establish `h` using `Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom e.toRingHom)) ι`. Rewrite `h` using `[Proj.opensRange_awayι]`. Conclude with `congrArg (fun U : (PN k N).Opens => (U : Set (PN k N))) h`.
-/
private theorem chart_holds : LPdCut.LChart := by
  intro k _ N i
  let e := chartE k N i
  let ι := Proj.awayι (grading k N) (MvPolynomial.X i) (X_mem i) one_pos
  have hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (RingEquiv.toCommRingCatIso e).isIso_hom
    infer_instance
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingHom) ≫ ι, inferInstance, ?_, ?_⟩
  · simp only [PNto, Category.assoc]
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (MvPolynomial.coeff _) (chartE_C k N i a)
  · have h := Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom e.toRingHom)) ι
    rw [Proj.opensRange_awayι] at h
    exact congrArg (fun U : (PN k N).Opens => (U : Set (PN k N))) h

/- English proof (translation)
Introduce `s`. Establish `hs : s ∈ (⊤ : (PN k d).Opens)` using `trivial`. Rewrite `hs` using `[← LSmoothPf.Dp_cover k d]`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hs`. Take `⟨j, hj, -, hr⟩` from `chart_holds k d i`.

Use `haveI := hj`. Establish `hU : j.opensRange = LPdCut.Dp k d i` using `TopologicalSpace.Opens.ext hr`. Use `⟨j.opensRange, isAffineOpen_opensRange j, hU ▸ hi, ?_⟩` and prove the remaining obligations. Establish `e1` using `j.appIso ⊤`. Rewrite `e1` using `[Scheme.Hom.image_top_eq_opensRange]`.

Establish `e` using `(e1 ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv`. Conclude with `⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩`.
-/
private theorem locNml (k : Type) [Field k] (d : ℕ) : TranscendenceTraces.LocNml (PN k d) := by
  intro s
  have hs : s ∈ (⊤ : (PN k d).Opens) := trivial
  rw [← LSmoothPf.Dp_cover k d] at hs
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  obtain ⟨j, hj, -, hr⟩ := chart_holds k d i
  haveI := hj
  have hU : j.opensRange = LPdCut.Dp k d i := TopologicalSpace.Opens.ext hr
  refine ⟨j.opensRange, isAffineOpen_opensRange j, hU ▸ hi, ?_⟩
  have e1 := j.appIso ⊤
  rw [Scheme.Hom.image_top_eq_opensRange] at e1
  have e := (e1 ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv, IsIntegrallyClosed.of_equiv e.symm⟩

/- English proof (translation)
Take `⟨j, hj, hc, hr⟩` from `chart_holds k 0 0`. Establish `htop : LPdCut.Dp k 0 0 = ⊤`. Use `LSmoothPf.Dp_cover k 0` as an intermediate fact. Simplify using `using this`. Establish `hjiso : IsIso j`.

Use `(isIso_iff_isOpenImmersion_and_surjective j).2 ⟨hj, ⟨fun x => ?_⟩⟩` and prove the remaining obligations. Establish `: x ∈ Set.range j`. Rewrite using `[hr, htop]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `this`.

Establish `hCiso : IsIso (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k))`. Establish `hb : Function.Bijective (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)` using `⟨MvPolynomial.C_injective _ _, MvPolynomial.C_surjective _⟩`. Conclude with `(RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ hb)).isIso_hom`. Establish `hP : PNto k 0 = inv j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k))`. Rewrite using `[← hc, IsIso.inv_hom_id_assoc]`.

Rewrite using `[hP]`. Use `infer_instance`.
-/
private theorem iso0 (k : Type) [Field k] : IsIso (PNto k 0) := by
  obtain ⟨j, hj, hc, hr⟩ := chart_holds k 0 0
  have htop : LPdCut.Dp k 0 0 = ⊤ := by
    have := LSmoothPf.Dp_cover k 0
    simpa using this
  have hjiso : IsIso j := by
    refine (isIso_iff_isOpenImmersion_and_surjective j).2 ⟨hj, ⟨fun x => ?_⟩⟩
    have : x ∈ Set.range j := by
      rw [hr, htop]
      trivial
    exact this
  have hCiso : IsIso (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    have hb : Function.Bijective (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k) :=
      ⟨MvPolynomial.C_injective _ _, MvPolynomial.C_surjective _⟩
    exact (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ hb)).isIso_hom
  have hP : PNto k 0 = inv j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin 0) k)) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  rw [hP]
  infer_instance

end UpperTheory.Gal.KunnethLefschetz.PnF

/- English proof (translation)
Unfold `UpperTheory.Gal.KunnethLefschetz.PnFacts`. Introduce `k _ d`. Conclude with `⟨⟨LProperPf.LProper_of k d, LSmoothPf.LSmooth_of PnF.chart_holds k d⟩, Cov.PNIntegral_of k d, PnF.locNml k d, PnF.iso0 k⟩`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.pnFacts_holds :
    UpperTheory.Gal.KunnethLefschetz.PnFacts := by
  unfold UpperTheory.Gal.KunnethLefschetz.PnFacts
  intro k _ d
  exact ⟨⟨LProperPf.LProper_of k d, LSmoothPf.LSmooth_of PnF.chart_holds k d⟩, Cov.PNIntegral_of k d, PnF.locNml k d, PnF.iso0 k⟩
