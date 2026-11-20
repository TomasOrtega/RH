import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapEqOfMemPtsIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFibreProjectiveCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveSingularPointsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneSubbundleSplitAtPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SaturatedCokernelVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationArithmeticCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalCurveSmoothNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOrderSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreeEqOrderSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointSumOverResiduesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.CechPic (cls)
open GlobalTheory.LB (toMod)
open Limits (cokernel IsZero)
open scoped ContDiff ENNReal

namespace GlobalTheory.ChernDegree

section Algebra

variable {κ Ω : Type} [Field κ] [Field Ω] [Algebra κ Ω] {C C' : Scheme.{0}} {f : C ⟶ Sp κ}
  {f' : C' ⟶ Sp Ω} {π : C' ⟶ C}

/- English proof (translation)
Use `letI := algebraΓOfHom f`. Use `letI := algebraΓOfHom f'`. Use `(isProper_and_exists_isAmpleLB_of_isProjOver hf).1` as an intermediate fact. Rewrite using `[← chi_congr Ω (Twist.unitTwistIso _), ← chi_congr κ (Twist.unitTwistIso _)]`. Conclude with `finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (FieldChangeInter.hdim_pull H hM n)`.
-/
theorem chi_toMod_pull (hf : IsProjOver f) (H : IsPullback π f' f (spMap (algebraMap κ Ω)))
    {M : LB C} (hM : M.IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    chi Ω (toMod (M.pull π)) = chi κ (toMod M) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  rw [← chi_congr Ω (Twist.unitTwistIso _), ← chi_congr κ (Twist.unitTwistIso _)]
  exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a)
    (FieldChangeInter.hdim_pull H hM n)

/- English proof (translation)
Use `letI := algebraΓOfHom f`. Use `letI := algebraΓOfHom f'`. Establish `h₀` using `LB.isLB_triv C`. Establish `h₁` using `Semi.LB.isLB_pull h₀ π`. Take `⟨e⟩` from `nonempty_twist_iso_of_cls_eq_zero (structureModule C) h₀ rfl`.

Take `⟨e'⟩` from `nonempty_twist_iso_of_cls_eq_zero (structureModule C') h₁ ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))`. Rewrite using `[← chi_congr κ e, ← chi_congr Ω e', chi_congr Ω (Twist.unitTwistIso _), chi_congr κ (Twist.unitTwistIso _)]`. Conclude with `chi_toMod_pull hf H h₀`.
-/
theorem chi_structureModule_pull (hf : IsProjOver f)
    (H : IsPullback π f' f (spMap (algebraMap κ Ω))) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    chi Ω (structureModule C') = chi κ (structureModule C) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h₀ := LB.isLB_triv C
  have h₁ := Semi.LB.isLB_pull h₀ π
  obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule C) h₀ rfl
  obtain ⟨e'⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule C') h₁
    ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))
  rw [← chi_congr κ e, ← chi_congr Ω e', chi_congr Ω (Twist.unitTwistIso _),
    chi_congr κ (Twist.unitTwistIso _)]
  exact chi_toMod_pull hf H h₀

/- English proof (translation)
Use `hC.isNoetherian` as an intermediate fact. Take `⟨G, φ, hG, hφ, hs⟩` from `GlobalTheory.T.rank_one_subbundle_split_at_points κ C hC.isProjOver F r hF _ (GlobalTheory.T.curve_singular_points_finite κ C hC)`. Establish `hQ` using `GlobalTheory.T.saturated_cokernel_vector_bundle C F G r φ hF hG hφ fun x => (em _).imp_right (hs x)`. Establish `hS : (ShortComplex.mk (satι φ) (cokernel.π _) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Conclude with `⟨_, satι φ, inferInstance, isVB_X₁_of_shortExact C _ 1 r hS (add_comm r 1 ▸ hF) hQ, hQ⟩`.
-/
theorem exists_line_subbundle [CharZero κ] [Algebra κ Γ(C, ⊤)] [IsIntegral C]
    (hC : IsProjCurve κ C) {F : C.Modules} {r : ℕ} (hF : IsVB F (r + 1)) :
    ∃ (L : C.Modules) (i : L ⟶ F) (_ : Mono i), IsVB L 1 ∧ IsVB (cokernel i) r := by
  have := hC.isNoetherian
  obtain ⟨G, φ, hG, hφ, hs⟩ := GlobalTheory.T.rank_one_subbundle_split_at_points κ C hC.isProjOver F r hF _ (GlobalTheory.T.curve_singular_points_finite κ C hC)
  have hQ := GlobalTheory.T.saturated_cokernel_vector_bundle C F G r φ hF hG hφ fun x => (em _).imp_right (hs x)
  have hS : (ShortComplex.mk (satι φ) (cokernel.π _) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact ⟨_, satι φ, inferInstance, isVB_X₁_of_shortExact C _ 1 r hS (add_comm r 1 ▸ hF) hQ, hQ⟩

/- English proof (translation)
Use `letI := algebraΓOfHom f`. Use `letI := algebraΓOfHom f'`. Establish `hf : IsProjOver f` using `(GlobalTheory.strHom_eq (f := f) fun _ => rfl) ▸ hC.isProjOver`. Establish `hf' : IsProjOver f'` using `ProjSpace.isProjOver_of_isPullback_spMap _ H hf`. Establish `: Flat (spMap (algebraMap κ Ω))` using `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)`.

Establish `: Flat π` using `MorphismProperty.of_isPullback H.flip this`. Establish `fin {F : C'.Modules} {r : ℕ} (h : IsVB F r) : FiniteCoh Ω F`. Use `h.isFiniteQC` as an intermediate fact. Use `finiteCoh_of_isProjOver (fun _ => rfl) F hf'`. Establish `one (L : C.Modules) (h : IsVB L 1) : degOfRank Ω ((Scheme.Modules.pullback π).obj L) 1 = degLB κ (det L 1)`.

Take `⟨φ⟩` from `nonempty_pullback_toMod_iso h.isLB_det π`. Rewrite using `[degOfRank_congr Ω ((Scheme.Modules.pullback π).mapIso h.isoDet ≪≫ φ), degOfRank, chi_toMod_pull hf H h.isLB_det, chi_structureModule_pull hf H, degLB_eq h.isLB_det]`. Simplify using the standard rewrite rules. Proceed by induction on `r with`. Consider the case `zero`.

Introduce `F hF`. Establish `h0` using `isVB_zero_iff.1 hF`. Establish `hS : (ShortComplex.mk (0 : F ⟶ F) (0 : F ⟶ F) Limits.zero_comp).ShortExact` using `{ exact := ShortComplex.exact_of_isZero_X₂ _ h0 mono_f := h0.mono _ epi_g := h0.epi _ }`. Take `⟨h₂, e⟩` from `VBExt.isVB_and_cls_det_of_shortExact C _ 0 0 hS hF hF`. Establish `e'` using `hC.degLB_of_cls_eq_add _ _ _ e`.

Rewrite using `[degOfRank, chi_eq_zero_of_isZero _ (isVB_zero_iff.1 (hF.pullback π))]`. Simplify using `only [Nat.add_zero] at e'`. Use linear arithmetic over natural numbers and integers. Consider the case `succ r ih`. Introduce `F hF`.

Take `⟨L, i, _, hL, hQ⟩` from `exists_line_subbundle hC hF`. Establish `hS : (ShortComplex.mk i (cokernel.π _) (cokernel.condition _)).ShortExact` using `{ exact := ShortComplex.exact_cokernel _ }`. Take `⟨h₂, e⟩` from `VBExt.isVB_and_cls_det_of_shortExact C _ 1 r hS hL hQ`. Establish `e'` using `hC.degLB_of_cls_eq_add _ _ _ e`. Use `hL.isQuasicoherent` as an intermediate fact.

Use `hF.isQuasicoherent` as an intermediate fact. Establish `e₂` using `degOfRank_shortExact (r := 1) (s := r) (QCoh.shortExact_map_pullback π hS) (fin (hL.pullback π)) (fin (hQ.pullback π))`. Rewrite using `[add_comm r 1]`. Conclude with `e₂.trans ((congrArg₂ (· + ·) (one L hL) (ih _ hQ)).trans e'.symm)`.
-/
theorem degOfRank_pull [CharZero κ] [IsIntegral C]
    (hC : letI := algebraΓOfHom f; IsProjCurve κ C)
    (H : IsPullback π f' f (spMap (algebraMap κ Ω))) (r : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    ∀ F : C.Modules, IsVB F r →
      degOfRank Ω ((Scheme.Modules.pullback π).obj F) r = degLB κ (det F r) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have hf : IsProjOver f := (GlobalTheory.strHom_eq (f := f) fun _ => rfl) ▸ hC.isProjOver
  have hf' : IsProjOver f' := ProjSpace.isProjOver_of_isPullback_spMap _ H hf
  have : Flat (spMap (algebraMap κ Ω)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat π := MorphismProperty.of_isPullback H.flip this
  have fin {F : C'.Modules} {r : ℕ} (h : IsVB F r) : FiniteCoh Ω F :=
    have := h.isFiniteQC
    finiteCoh_of_isProjOver (fun _ => rfl) F hf'
  have one (L : C.Modules) (h : IsVB L 1) :
      degOfRank Ω ((Scheme.Modules.pullback π).obj L) 1 = degLB κ (det L 1) := by
    obtain ⟨φ⟩ := nonempty_pullback_toMod_iso h.isLB_det π
    rw [degOfRank_congr Ω ((Scheme.Modules.pullback π).mapIso h.isoDet ≪≫ φ), degOfRank,
      chi_toMod_pull hf H h.isLB_det, chi_structureModule_pull hf H, degLB_eq h.isLB_det]
    simp
  induction r with
  | zero =>
    intro F hF
    have h0 := isVB_zero_iff.1 hF
    have hS : (ShortComplex.mk (0 : F ⟶ F) (0 : F ⟶ F) Limits.zero_comp).ShortExact :=
      { exact := ShortComplex.exact_of_isZero_X₂ _ h0
        mono_f := h0.mono _
        epi_g := h0.epi _ }
    obtain ⟨h₂, e⟩ := VBExt.isVB_and_cls_det_of_shortExact C _ 0 0 hS hF hF
    have e' := hC.degLB_of_cls_eq_add _ _ _ e
    rw [degOfRank, chi_eq_zero_of_isZero _ (isVB_zero_iff.1 (hF.pullback π))]
    simp only [Nat.add_zero] at e'
    omega
  | succ r ih =>
    intro F hF
    obtain ⟨L, i, _, hL, hQ⟩ := exists_line_subbundle hC hF
    have hS : (ShortComplex.mk i (cokernel.π _) (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨h₂, e⟩ := VBExt.isVB_and_cls_det_of_shortExact C _ 1 r hS hL hQ
    have e' := hC.degLB_of_cls_eq_add _ _ _ e
    have := hL.isQuasicoherent
    have := hF.isQuasicoherent
    have e₂ := degOfRank_shortExact (r := 1) (s := r) (QCoh.shortExact_map_pullback π hS)
      (fin (hL.pullback π)) (fin (hQ.pullback π))
    rw [add_comm r 1]
    exact e₂.trans ((congrArg₂ (· + ·) (one L hL) (ih _ hQ)).trans e'.symm)

end Algebra

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

/- English proof (translation)
Establish `hC` using `GlobalTheory.T.rational_fibre_projective_curve k X p hX`. Use `hC.isIntegral` as an intermediate fact. Establish `e : spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ) = spMap (Int.castRingHom ℂ)`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`.

Establish `H₀ : IsPullback (cxFibre.fst p) (cxFibre.snd p) (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ))`. Rewrite using `[e]`. Conclude with `IsPullback.of_hasPullback _ _`. Set `π` to `(ratFibre.isPullback p).lift (cxFibre.fst p) (cxFibre.snd p ≫ spMap (algebraMap ℚ ℂ)) (by rw [Category.assoc]; exact H₀.w)`. Establish `hπ : π ≫ ratFibre.fst p = cxFibre.fst p` using `IsPullback.lift_fst _ _ _ _`.

Establish `H : IsPullback π (cxFibre.snd p) (ratFibre.snd p) (spMap (algebraMap ℚ ℂ))` using `IsPullback.of_right (hπ ▸ H₀) (IsPullback.lift_snd _ _ _ _) (ratFibre.isPullback p)`. Establish `hF` using `hE.pullback (ratFibre.fst p)`. Establish `i : (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback (ratFibre.fst p)).obj E) ≅ (Scheme.Modules.pullback (cxFibre.fst p)).obj E` using `(Scheme.Modules.pullbackComp π _).app E ≪≫ (Scheme.Modules.pullbackCongr hπ).app E`. Rewrite using `[ratDeg_eq_degLB hE.isLB_det, degLB_congr (Semi.LB.isLB_pull hE.isLB_det _) hF.isLB_det (hE.lbIso_det_pullback _), cxDeg, ← degOfRank_congr ℂ i]`. Conclude with `degOfRank_pull hC H r _ hF`.
-/
theorem cxDeg_eq_ratDeg (hX : IsArithVar p 1) {E : X.Modules} {r : ℕ} (hE : IsVB E r) :
    cxDeg p E r = ratDeg p (det E r) := by
  have hC := GlobalTheory.T.rational_fibre_projective_curve k X p hX
  have := hC.isIntegral
  have e : spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ) = spMap (Int.castRingHom ℂ) := by
    rw [← Spec.map_comp]
    congr 1
  have H₀ : IsPullback (cxFibre.fst p) (cxFibre.snd p) (p ≫ spMap (Int.castRingHom k))
      (spMap (algebraMap ℚ ℂ) ≫ spMap (Int.castRingHom ℚ)) := by
    rw [e]
    exact IsPullback.of_hasPullback _ _
  let π := (ratFibre.isPullback p).lift (cxFibre.fst p) (cxFibre.snd p ≫ spMap (algebraMap ℚ ℂ))
    (by rw [Category.assoc]; exact H₀.w)
  have hπ : π ≫ ratFibre.fst p = cxFibre.fst p := IsPullback.lift_fst _ _ _ _
  have H : IsPullback π (cxFibre.snd p) (ratFibre.snd p) (spMap (algebraMap ℚ ℂ)) :=
    IsPullback.of_right (hπ ▸ H₀) (IsPullback.lift_snd _ _ _ _) (ratFibre.isPullback p)
  have hF := hE.pullback (ratFibre.fst p)
  have i : (Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback (ratFibre.fst p)).obj E) ≅
      (Scheme.Modules.pullback (cxFibre.fst p)).obj E :=
    (Scheme.Modules.pullbackComp π _).app E ≪≫ (Scheme.Modules.pullbackCongr hπ).app E
  rw [ratDeg_eq_degLB hE.isLB_det, degLB_congr (Semi.LB.isLB_pull hE.isLB_det _) hF.isLB_det
    (hE.lbIso_det_pullback _), cxDeg, ← degOfRank_congr ℂ i]
  exact degOfRank_pull hC H r _ hF

section Smooth

open ReciprocityTheory.AnForm.M

variable {A B : LB X}

/- English proof (translation)
Use `CxPts.compactSpace σ hX` as an intermediate fact. Use `CxPts.t2Space_cxPts_of_isProjOver σ hX` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ := σ) hX` as an intermediate fact. Conclude with `(Weight.chernInt_eq_mInt R h measurable_const).1.2 (mIntegrableCont _ _ (fun _ => Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 h)) _ continuous_const)`.
-/
theorem chernIntegrableOn_one (hX : IsProjOver p) (R : AnRead p σ 1) {φ : Weight p σ B}
    (h : φ.IsCInf) : φ.ChernIntegrableOn 1 univ fun _ => 1 := by
  have := CxPts.compactSpace σ hX
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hX
  exact (Weight.chernInt_eq_mInt R h measurable_const).1.2 (mIntegrableCont _ _
    (fun _ => Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 h)) _ continuous_const)

/- English proof (translation)
Use `CxPts.compactSpace σ hX` as an intermediate fact. Use `CxPts.t2Space_cxPts_of_isProjOver σ hX` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ := σ) hX` as an intermediate fact. Establish `s'` using `(Weight.isCInf_iff_isSmooth R).1 h'`. Establish `s` using `(Weight.isCInf_iff_isSmooth R).1 h`.

Establish `e (P : LocPot (CxPts p σ)) : (Fin.cons P finZeroElim : Fin (0 + 1) → _) = fun _ => P`. Use function extensionality and compare the values at `fun i => by rw [Subsingleton.elim (α := Fin 1) i 0]; rfl`. Establish `I {P} (hP : IsPotential R.finAtlas P) : MIntegrable R.finAtlas (Fin.cons P finZeroElim) fun _ => 1` using `e P ▸ mIntegrableCont _ _ (fun _ => hP) _ continuous_const`. Establish `H` using `mIntAdd R.finAtlas _ _ finZeroElim (Weight.isPotential_locPot s') (Weight.isPotential_locPot s) finZeroElim _ (I (Weight.isPotential_locPot s')) (I (Weight.isPotential_locPot s))`. Rewrite `H` using `[e, e, e]`.

Rewrite using `[(Weight.chernInt_eq_mInt R h measurable_const).2 (chernIntegrableOn_one hX R h), (Weight.chernInt_eq_mInt R h' measurable_const).2 (chernIntegrableOn_one hX R h'), (Weight.chernInt_eq_mInt R (h'.tens h) measurable_const).2 (chernIntegrableOn_one hX R (h'.tens h)), ← H]`. Conclude with `SameForm.mInt_eq (fun _ => s'.sameForm_tens s R.isAlgAtlas_finAtlas) _`.
-/
theorem chernInt_tens (hX : IsProjOver p) (R : AnRead p σ 1) {ψ : Weight p σ A} {φ : Weight p σ B}
    (h' : ψ.IsCInf) (h : φ.IsCInf) : (ψ.tens φ).chernInt 1 univ (fun _ => 1) =
      ψ.chernInt 1 univ (fun _ => 1) + φ.chernInt 1 univ fun _ => 1 := by
  have := CxPts.compactSpace σ hX
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hX
  have s' := (Weight.isCInf_iff_isSmooth R).1 h'
  have s := (Weight.isCInf_iff_isSmooth R).1 h
  have e (P : LocPot (CxPts p σ)) : (Fin.cons P finZeroElim : Fin (0 + 1) → _) = fun _ => P :=
    funext fun i => by rw [Subsingleton.elim (α := Fin 1) i 0]; rfl
  have I {P} (hP : IsPotential R.finAtlas P) : MIntegrable R.finAtlas (Fin.cons P finZeroElim)
      fun _ => 1 := e P ▸ mIntegrableCont _ _ (fun _ => hP) _ continuous_const
  have H := mIntAdd R.finAtlas _ _ finZeroElim (Weight.isPotential_locPot s')
    (Weight.isPotential_locPot s) finZeroElim _ (I (Weight.isPotential_locPot s'))
    (I (Weight.isPotential_locPot s))
  rw [e, e, e] at H
  rw [(Weight.chernInt_eq_mInt R h measurable_const).2 (chernIntegrableOn_one hX R h),
    (Weight.chernInt_eq_mInt R h' measurable_const).2 (chernIntegrableOn_one hX R h'),
    (Weight.chernInt_eq_mInt R (h'.tens h) measurable_const).2
      (chernIntegrableOn_one hX R (h'.tens h)), ← H]
  exact SameForm.mInt_eq (fun _ => s'.sameForm_tens s R.isAlgAtlas_finAtlas) _

variable [IsIntegral X]

/- English proof (translation)
Use `hX.finite_emb` as an intermediate fact. Take `⟨S, h₁, h₂, h₃⟩` from `GlobalTheory.T.rational_degree_eq_order_sum k X p (GlobalTheory.T.rational_fibre_projective_curve k X p hX) B hB s h0`. Rewrite using `[finsum_congr fun σ => GlobalTheory.T.chern_integral_eq_order_sum k X p hX σ (hs σ) B (φ σ) (h σ) s h0, GlobalTheory.T.complex_point_sum_over_residues k X p S (fun x => (secOrd hB s x : ℝ)) h₂ fun x hx hm => h₁ x hx fun h' => hm (by rw [secOrd_eq_zero hB h', Nat.cast_zero]), h₃]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem finsum_chernInt_of_sec (hX : IsArithVar p 1) (hs : GenSmooth p 1) (hB : B.IsLB)
    {φ : ∀ σ, Weight p σ B} (h : ∀ σ, (φ σ).IsCInf) (s : B.Sec)
    (h0 : genericPoint X ∈ nonzeroLocus s) :
    ∑ᶠ σ, (φ σ).chernInt 1 univ (fun _ => 1) = ratDeg p B := by
  have := hX.finite_emb
  obtain ⟨S, h₁, h₂, h₃⟩ := GlobalTheory.T.rational_degree_eq_order_sum k X p (GlobalTheory.T.rational_fibre_projective_curve k X p hX) B hB s h0
  rw [finsum_congr fun σ => GlobalTheory.T.chern_integral_eq_order_sum k X p hX σ (hs σ) B (φ σ) (h σ) s h0,
    GlobalTheory.T.complex_point_sum_over_residues k X p S (fun x => (secOrd hB s x : ℝ)) h₂ fun x hx hm => h₁ x hx fun h' =>
      hm (by rw [secOrd_eq_zero hB h', Nat.cast_zero]), h₃]
  push_cast
  rfl

/- English proof (translation)
Use `hX.finite_emb` as an intermediate fact. Use `Fintype.ofFinite (k →+* ℂ)` as an intermediate fact. Use `hX.isLocallyNoetherian` as an intermediate fact. Establish `hC` using `GlobalTheory.T.rational_fibre_projective_curve k X p hX`. Use `hC.isIntegral` as an intermediate fact.

Take `⟨N, i, _, hi⟩` from `hX.isProjOver`. Set `H` to `(ProjSpace.hermitianTwistingSheaf k N).pull i hi`. Establish `hH : IsAmpleLB H.B` using `(isAmple_projective_O_one k N).pull_of_isClosedImmersion i`. Take `⟨n, h₁, h₂⟩` from `(tendsto_natCast_atTop_atTop.eventually ((hH.eventually_exists_finite_subset_nonzeroLocus hB (finite_singleton (genericPoint X))).and (hH.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) (finite_singleton (genericPoint X))))).exists`. Establish `hM` using `(H.pow n).isLB`.

Establish `hT` using `CechPic.isLB_tens hB hM`. Establish `eM : cls _ hM = (n : ℤ) • cls H.B hH.isLB` using `(CechPic.cls_lbPow hH.isLB n hM).trans (natCast_zsmul _ _).symm`. Take `⟨s, hs₁⟩` from `h₁ _ hT (by rw [CechPic.cls_tens hB hM, eM])`. Take `⟨t, ht⟩` from `h₂ _ hM (by rw [eM, cls_triv, zero_add])`. Establish `e₁` using `finsum_chernInt_of_sec hX hs hT (fun σ => (h σ).tens ((H.pow n).cInf σ)) s (hs₁ rfl)`.

Establish `e₂` using `finsum_chernInt_of_sec hX hs hM (H.pow n).cInf t (ht rfl)`. Establish `e₃ : ratDeg p (CechPic.tens B (H.pow n).B) = ratDeg p B + ratDeg p (H.pow n).B`. Rewrite using `[ratDeg_eq_degLB hT, ratDeg_eq_degLB hB, ratDeg_eq_degLB hM]`. Use `hC.degLB_of_cls_eq_add (Semi.LB.isLB_pull hT _) (Semi.LB.isLB_pull hB _) (Semi.LB.isLB_pull hM _) ?_` and prove the remaining obligations. Rewrite using `[CechPic.cls_pull hT, CechPic.cls_pull hB, CechPic.cls_pull hM, CechPic.cls_tens hB hM, map_add]`.

Rewrite `e₁` using `[finsum_congr fun σ => (hs σ).elim fun R => chernInt_tens hX.isProjOver R (h σ) ((H.pow n).cInf σ), finsum_add_distrib (toFinite _) (toFinite _), e₂, e₃, Int.cast_add]`. Conclude with `add_right_cancel e₁`.
-/
theorem finsum_chernInt (hX : IsArithVar p 1) (hs : GenSmooth p 1) (hB : B.IsLB)
    {φ : ∀ σ, Weight p σ B} (h : ∀ σ, (φ σ).IsCInf) :
    ∑ᶠ σ, (φ σ).chernInt 1 univ (fun _ => 1) = ratDeg p B := by
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have := hX.isLocallyNoetherian
  have hC := GlobalTheory.T.rational_fibre_projective_curve k X p hX
  have := hC.isIntegral
  obtain ⟨N, i, _, hi⟩ := hX.isProjOver
  let H := (ProjSpace.hermitianTwistingSheaf k N).pull i hi
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k N).pull_of_isClosedImmersion i
  obtain ⟨n, h₁, h₂⟩ := (tendsto_natCast_atTop_atTop.eventually
    ((hH.eventually_exists_finite_subset_nonzeroLocus hB (finite_singleton (genericPoint X))).and
      (hH.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X)
        (finite_singleton (genericPoint X))))).exists
  have hM := (H.pow n).isLB
  have hT := CechPic.isLB_tens hB hM
  have eM : cls _ hM = (n : ℤ) • cls H.B hH.isLB :=
    (CechPic.cls_lbPow hH.isLB n hM).trans (natCast_zsmul _ _).symm
  obtain ⟨s, hs₁⟩ := h₁ _ hT (by rw [CechPic.cls_tens hB hM, eM])
  obtain ⟨t, ht⟩ := h₂ _ hM (by rw [eM, cls_triv, zero_add])
  have e₁ := finsum_chernInt_of_sec hX hs hT (fun σ => (h σ).tens ((H.pow n).cInf σ)) s (hs₁ rfl)
  have e₂ := finsum_chernInt_of_sec hX hs hM (H.pow n).cInf t (ht rfl)
  have e₃ : ratDeg p (CechPic.tens B (H.pow n).B) = ratDeg p B + ratDeg p (H.pow n).B := by
    rw [ratDeg_eq_degLB hT, ratDeg_eq_degLB hB, ratDeg_eq_degLB hM]
    refine hC.degLB_of_cls_eq_add (Semi.LB.isLB_pull hT _) (Semi.LB.isLB_pull hB _)
      (Semi.LB.isLB_pull hM _) ?_
    rw [CechPic.cls_pull hT, CechPic.cls_pull hB, CechPic.cls_pull hM, CechPic.cls_tens hB hM, map_add]
  rw [finsum_congr fun σ => (hs σ).elim fun R =>
    chernInt_tens hX.isProjOver R (h σ) ((H.pow n).cInf σ), finsum_add_distrib (toFinite _)
    (toFinite _), e₂, e₃, Int.cast_add] at e₁
  exact add_right_cancel e₁

end Smooth

section Regular

variable {B : LB X} {D : ℕ} {φ : Weight p σ B} {y : CxPts p σ}

variable (φ D) in

def ChartSmooth : Prop := ∀ (c : AlgChart p σ D) (i : B.ι), ContDiffOn ℝ ∞ (φ.φ i ∘ c.e.symm)
  (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i))

/- English proof (translation)
Introduce `c i` and use `contDiffOn_chart (h i) c`.
-/
theorem chartSmooth_of_isCInf (h : φ.IsCInf) : ChartSmooth D φ := fun c i => contDiffOn_chart (h i) c

/- English proof (translation)
Establish `ho` using `isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B.U j))`. Establish `hm` using `mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)`. Establish `hg` using `c.holo _ (B.g i j).val`. Establish `h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B.U j), (ev p σ _ (B.g i j).val ∘ c.e.symm) v ≠ 0` using `fun v hv => ev_ne_zero hv.2 (B.g i j).isUnit`. Establish `e` using `ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho ((h c i).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩) (contDiffOn_log_normSq ho hg h0) (-1) hm`.

Establish `e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ (B.g i j).val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0`. Use extensionality with `a b`. Conclude with `ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b`. Rewrite `e` using `[e₀, smul_zero, add_zero]`. Use `Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e` and prove the remaining obligations.

Use `filter_upwards [ho.mem_nhds hm] with v hv`. Rewrite using `[φ.trans i j _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, neg_one_mul, sub_eq_add_neg]`. Both sides reduce to the same expression.
-/
theorem ChartSmooth.hess_eq (h : ChartSmooth D φ) (c : AlgChart p σ D) (hy : y ∈ c.e.source)
    {i j : B.ι} (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) :
    c.hess φ j y = c.hess φ i y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i ⊓ B.U j))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨hi, hj⟩)
  have hg := c.holo _ (B.g i j).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (B.U i ⊓ B.U j),
      (ev p σ _ (B.g i j).val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 (B.g i j).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((h c i).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).1⟩)
    (contDiffOn_log_normSq ho hg h0) (-1) hm
  have e₀ : cHess D (fun w => ((Real.log (‖(ev p σ _ (B.g i j).val ∘ c.e.symm) w‖ ^ 2) : ℝ) : ℂ))
      (c.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [φ.trans i j _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, neg_one_mul, sub_eq_add_neg]
  rfl

/- English proof (translation)
Establish `ho` using `isOpen_over c.e c'.e.open_source`. Establish `hm` using `mem_over c.e hy hy'`. Establish `e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm` using `eventually_of_mem (ho.mem_nhds hm) fun v hv => by`. Simplify using `only [Function.comp_apply, c'.e.left_inv hv.2]`. Establish `e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y` using `congrArg c'.e (c.e.left_inv hy)`.

Establish `hd : ContDiffAt ℝ 2 (fun v => φ.φ (pick φ.isLB y) (c'.e.symm v)) (c'.e y)` using `((h c' _).contDiffAt ((isOpen_over c'.e (isOpen_ptsIn _)).mem_nhds (mem_over c'.e hy' (mem_pick _ y)))).of_le (by norm_cast)`. Rewrite using `[AlgChart.chernDens, AlgChart.chernDens, AlgChart.hess, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (c.holo_trans c') (e₂ ▸ Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd), e₂, Complex.re_ofReal_m …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ChartSmooth.chernDens_trans (h : ChartSmooth D φ) (c c' : AlgChart p σ D)
    (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) :
    c.chernDens φ y = ‖transDet c.e c'.e y‖ ^ 2 * c'.chernDens φ y := by
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have e : (fun v => (φ.φ (pick φ.isLB y) (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)]
      (fun v => (φ.φ (pick φ.isLB y) (c'.e.symm v) : ℂ)) ∘ c'.e ∘ c.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      simp only [Function.comp_apply, c'.e.left_inv hv.2]
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hd : ContDiffAt ℝ 2 (fun v => φ.φ (pick φ.isLB y) (c'.e.symm v)) (c'.e y) :=
    ((h c' _).contDiffAt ((isOpen_over c'.e (isOpen_ptsIn _)).mem_nhds
      (mem_over c'.e hy' (mem_pick _ y)))).of_le (by norm_cast)
  rw [AlgChart.chernDens, AlgChart.chernDens, AlgChart.hess, AlgChart.hess,
    ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (c.holo_trans c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd), e₂, Complex.re_ofReal_mul, transDet]
  ring

/- English proof (translation)
Establish `hj` using `mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl) (mem_pick (φ.pull π hπ).isLB z) PUnit.unit`. Establish `hS : IsOpen (c'.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source)` using `c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map π hπ _))`. Rewrite using `[AlgChart.chernDens, AlgChart.chernDens, h.hess_eq c hz' hj (mem_pick _ _), AlgChart.hess, AlgChart.hess, ← he z hz hz', ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]`. Use `filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv`. Establish `e₁ : c.e.symm v = PtsOver.map π hπ _ (c'.e.symm v)`.

Use `he _ hv.2.1 hv.2.2` as an intermediate fact. Rewrite `this` using `[c'.e.right_inv hv.1]`. Conclude with `(congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)`. Rewrite using `[e₁]`. Conclude with `congrArg _ (φ.pull_φ π hπ _ _)`.
-/
theorem ChartSmooth.chernDens_pull (h : ChartSmooth D φ) {q : Y ⟶ Sp k} {π : Y ⟶ X}
    (hπ : π ≫ p = q) (c : AlgChart p σ D) (c' : AlgChart q σ D) {z : CxPts q σ}
    (hz : z ∈ c'.e.source) (hz' : PtsOver.map π hπ _ z ∈ c.e.source)
    (he : ∀ w ∈ c'.e.source, PtsOver.map π hπ _ w ∈ c.e.source →
      c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) :
    c'.chernDens (φ.pull π hπ) z = c.chernDens φ (PtsOver.map π hπ _ z) := by
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (φ.pull π hπ).isLB z) PUnit.unit
  have hS : IsOpen (c'.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
    c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map π hπ _))
  rw [AlgChart.chernDens, AlgChart.chernDens, h.hess_eq c hz' hj (mem_pick _ _), AlgChart.hess,
    AlgChart.hess, ← he z hz hz', ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
  filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv
  have e₁ : c.e.symm v = PtsOver.map π hπ _ (c'.e.symm v) := by
    have := he _ hv.2.1 hv.2.2
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)
  rw [e₁]
  exact congrArg _ (φ.pull_φ π hπ _ _)

/- English proof (translation)
Take `⟨T, hT, hT', hf, hc⟩` from `FlagPull.exists_finite_exceptional k X p Y q hp hq π hπ hg hd σ`. Use `CxPts.t2Space_cxPts_of_isProjOver σ hp.isProjOver` as an intermediate fact. Use `CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver` as an intermediate fact.

Use `GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq 1 one_ne_zero (CxPts p σ) (CxPts q σ) (AlgChart p σ 1) (AlgChart q σ 1) _ _ _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_) (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_) _ (PtsOver.continuous_map π hπ _) …` and prove the remaining obligations. Rewrite using `[h.chernDens_trans c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]`. Rewrite using `[h'.chernDens_trans c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]`. Take `⟨c, c', h₁, h₂, h₃⟩` from `hc z hz`. Conclude with `⟨c, c', h₁, h₂, fun w hw hw' => ⟨h₃ w hw hw', by rw [h.chernDens_pull hπ c c' hw hw' h₃]⟩⟩`.
-/
theorem ChartSmooth.chernPart_pull [IsIntegral X] [IsIntegral Y] (h : ChartSmooth 1 φ)
    {q : Y ⟶ Sp k} (hp : IsArithVar p 1) (hq : IsArithVar q 1) {π : Y ⟶ X} (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)
    (h' : ChartSmooth 1 (φ.pull π hπ)) (ε : ℤˣ) : (φ.pull π hπ).chernPart 1 ε univ =
      π.residueDegree (genericPoint Y) * φ.chernPart 1 ε univ := by
  obtain ⟨T, hT, hT', hf, hc⟩ :=
    FlagPull.exists_finite_exceptional k X p Y q hp hq π hπ hg hd σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  refine GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq 1 one_ne_zero (CxPts p σ) (CxPts q σ) (AlgChart p σ 1) (AlgChart q σ 1) _ _ _ _
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    _ (PtsOver.continuous_map π hπ _) T hT hT' _ hd hf fun z hz => ?_
  · rw [h.chernDens_trans c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [h'.chernDens_trans c c' hy hy', mul_left_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, c', h₁, h₂, h₃⟩ := hc z hz
    exact ⟨c, c', h₁, h₂, fun w hw hw' => ⟨h₃ w hw hw', by rw [h.chernDens_pull hπ c c' hw hw' h₃]⟩⟩

/- English proof (translation)
Establish `e` using `h.chernPart_pull hp hq hπ hg hd h'`. Establish `key (ε) (H : IntegrableOn (fun _ => (1 : ℝ)) univ ((φ.pull π hπ).chernPart 1 ε)) : IntegrableOn (fun _ => (1 : ℝ)) univ (φ.chernPart 1 ε)`. Rewrite `H`, the goal using `[integrableOn_const_iff]`. Use `H.imp_right fun H => lt_top_iff_ne_top.2 fun h0 => H.ne ?_` and prove the remaining obligations. Rewrite using `[e, h0, ENNReal.mul_top (Nat.cast_ne_zero.2 hd)]`.

Use `⟨⟨key _ hi.1, key _ hi.2⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one, measureReal_def, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]`.
-/
theorem ChartSmooth.chernInt_pull [IsIntegral X] [IsIntegral Y] (h : ChartSmooth 1 φ)
    {q : Y ⟶ Sp k} (hp : IsArithVar p 1) (hq : IsArithVar q 1) {π : Y ⟶ X} (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)
    (h' : ChartSmooth 1 (φ.pull π hπ)) (hi : (φ.pull π hπ).ChernIntegrableOn 1 univ fun _ => 1) :
    φ.ChernIntegrableOn 1 univ (fun _ => 1) ∧ (φ.pull π hπ).chernInt 1 univ (fun _ => 1) =
      π.residueDegree (genericPoint Y) * φ.chernInt 1 univ fun _ => 1 := by
  have e := h.chernPart_pull hp hq hπ hg hd h'
  have key (ε) (H : IntegrableOn (fun _ => (1 : ℝ)) univ ((φ.pull π hπ).chernPart 1 ε)) :
      IntegrableOn (fun _ => (1 : ℝ)) univ (φ.chernPart 1 ε) := by
    rw [integrableOn_const_iff] at H ⊢
    refine H.imp_right fun H => lt_top_iff_ne_top.2 fun h0 => H.ne ?_
    rw [e, h0, ENNReal.mul_top (Nat.cast_ne_zero.2 hd)]
  refine ⟨⟨key _ hi.1, key _ hi.2⟩, ?_⟩
  simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one,
    measureReal_def, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]

end Regular

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r}

/- English proof (translation)
Use `((H σ).detWeight (c.pull h.isVB π) z hz).congr ?_` and prove the remaining obligations. Use `filter_upwards [(isOpen_ptsIn (π ⁻¹ᵁ c.U)).mem_nhds hz] with w hw`. Conclude with `congrArg (fun A => -Real.log (Matrix.det A).re) ((h.met σ).pull_G π rfl c hw).symm`.
-/
theorem cInfAt_detWeight_map {π : Y ⟶ X} (H : (h.pull π rfl).IsCInf) (c : Chart E r)
    {z : CxPts (π ≫ p) σ} (hz : PtsOver.map π rfl _ z ∈ ptsIn p σ c.U) :
    CInfAt (fun w => (h.met σ).detWeight.φ c (PtsOver.map π rfl _ w)) z := by
  refine ((H σ).detWeight (c.pull h.isVB π) z hz).congr ?_
  filter_upwards [(isOpen_ptsIn (π ⁻¹ᵁ c.U)).mem_nhds hz] with w hw
  exact congrArg (fun A => -Real.log (Matrix.det A).re) ((h.met σ).pull_G π rfl c hw).symm

/- English proof (translation)
Introduce `j z hz` and use `(cInfAt_detWeight_map H _ (mem_of_mem_linComb (m := fun _ => PtsOver.map π rfl _ z) (fun _ => rfl) hz PUnit.unit)).congr (.of_forall fun w => Weight.pull_φ _ π rfl j w)`.
-/
theorem isCInf_detWeight_pull {π : Y ⟶ X} (H : (h.pull π rfl).IsCInf) :
    ((h.met σ).detWeight.pull π rfl).IsCInf := fun j z hz =>
  (cInfAt_detWeight_map H _ (mem_of_mem_linComb (m := fun _ => PtsOver.map π rfl _ z)
    (fun _ => rfl) hz PUnit.unit)).congr (.of_forall fun w => Weight.pull_φ _ π rfl j w)

/- English proof (translation)
Introduce `c i`. Use `(contDiffOn_chart (S := c.e.source ∩ ptsIn p σ ((det E r).U i)) (fun y hy => ?_) c).mono fun v hv => ⟨hv.1, c.e.map_target hv.1, hv.2⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `exists_map_eq_of_mem_ptsIn rfl (c.source_subset hy.1)`. Conclude with `VInfAt.of_isOpenImmersion c.U.ι rfl (cInfAt_detWeight_map (H _ _ (GlobalTheory.T.algebraic_chart_smooth k X p σ 1 c)) i hy.2)`.
-/
theorem chartSmooth_detWeight (H : h.IsCInfNorm) : ChartSmooth 1 (h.met σ).detWeight := by
  intro c i
  refine (contDiffOn_chart (S := c.e.source ∩ ptsIn p σ ((det E r).U i)) (fun y hy => ?_) c).mono
    fun v hv => ⟨hv.1, c.e.map_target hv.1, hv.2⟩
  obtain ⟨z, rfl⟩ := exists_map_eq_of_mem_ptsIn rfl (c.source_subset hy.1)
  exact VInfAt.of_isOpenImmersion c.U.ι rfl
    (cInfAt_detWeight_map (H _ _ (GlobalTheory.T.algebraic_chart_smooth k X p σ 1 c)) i hy.2)

/- English proof (translation)
Introduce `k _ X p hX E r h H`. Use `hX.isIntegral` as an intermediate fact. Use `hX.finite_emb` as an intermediate fact. Take `⟨Y, _, ν, _, hn, hY, hg, hd⟩` from `GlobalTheory.T.normalisation_arithmetic_curve k X p hX`. Establish `hl` using `GlobalTheory.T.normal_curve_smooth_near_point k Y _ hY hn`.

Establish `hs : GenSmooth (ν ≫ p) 1` using `fun σ => ⟨⟨AlgChart _ σ 1, id, fun y => by`. Take `⟨W, hW, _⟩` from `hl σ y`. Take `⟨U, x, hU, hz, hx⟩` from `ModelCharts.exists_etale_coords_of_opens (ν ≫ p) 1 W (mem_ptsIn.1 hW)`. Take `⟨c, hc, -⟩` from `AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz)`. Conclude with `⟨c, hc⟩⟩⟩`.

Establish `hc (σ) : ((h.met σ).detWeight.pull ν rfl).IsCInf` using `isCInf_detWeight_pull (H.pull_isCInf_of_local ν hl)`. Establish `key (σ)` using `(chartSmooth_detWeight (σ := σ) H).chernInt_pull hX hY rfl hg hd (chartSmooth_of_isCInf (hc σ)) ((hs σ).elim fun R => chernIntegrableOn_one hY.isProjOver R (hc σ))`. Use `⟨fun σ => (key σ).1, mul_left_cancel₀ (Nat.cast_ne_zero.2 hd) ?_⟩` and prove the remaining obligations. Establish `e` using `finsum_chernInt hY hs (Semi.LB.isLB_pull h.isVB.isLB_det ν) hc`. Rewrite `e` using `[finsum_congr fun σ => (key σ).2, ← mul_finsum, GlobalTheory.T.rational_degree_pullback_finite k X p Y ν (GlobalTheory.T.rational_fibre_projective_curve k X p hX) (GlobalTheory.T.rational_fibre_projective_curve k Y _ hY) hg _ h.isVB.isLB_det]`.

Rewrite using `[cxDeg_eq_ratDeg hX h.isVB]`. Conclude with `e.trans (by push_cast; rfl)`.
-/
theorem first_chern_integral_eq_degree : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInfNorm → h.FirstChernIntegrable ∧ h.first_chern_integral = cxDeg p E r := by
  intro k _ X p hX E r h H
  have := hX.isIntegral
  have := hX.finite_emb
  obtain ⟨Y, _, ν, _, hn, hY, hg, hd⟩ := GlobalTheory.T.normalisation_arithmetic_curve k X p hX
  have hl := GlobalTheory.T.normal_curve_smooth_near_point k Y _ hY hn
  have hs : GenSmooth (ν ≫ p) 1 := fun σ => ⟨⟨AlgChart _ σ 1, id, fun y => by
    obtain ⟨W, hW, _⟩ := hl σ y
    obtain ⟨U, x, hU, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens (ν ≫ p) 1 W
      (mem_ptsIn.1 hW)
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU x hx (mem_ptsIn.2 hz)
    exact ⟨c, hc⟩⟩⟩
  have hc (σ) : ((h.met σ).detWeight.pull ν rfl).IsCInf :=
    isCInf_detWeight_pull (H.pull_isCInf_of_local ν hl)
  have key (σ) := (chartSmooth_detWeight (σ := σ) H).chernInt_pull hX hY rfl hg hd
    (chartSmooth_of_isCInf (hc σ)) ((hs σ).elim fun R => chernIntegrableOn_one hY.isProjOver R (hc σ))
  refine ⟨fun σ => (key σ).1, mul_left_cancel₀ (Nat.cast_ne_zero.2 hd) ?_⟩
  have e := finsum_chernInt hY hs (Semi.LB.isLB_pull h.isVB.isLB_det ν) hc
  rw [finsum_congr fun σ => (key σ).2, ← mul_finsum, GlobalTheory.T.rational_degree_pullback_finite k X p Y ν
    (GlobalTheory.T.rational_fibre_projective_curve k X p hX) (GlobalTheory.T.rational_fibre_projective_curve k Y _ hY) hg _ h.isVB.isLB_det] at e
  rw [cxDeg_eq_ratDeg hX h.isVB]
  exact e.trans (by push_cast; rfl)

end GlobalTheory.ChernDegree
