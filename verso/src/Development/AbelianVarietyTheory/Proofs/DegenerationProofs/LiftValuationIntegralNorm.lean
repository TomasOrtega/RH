import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegraStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartsIsoLabelsOfThetaPointAndValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationRecognitionOfAbelianPartsIsoLabelsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisationGeneratingSectionPullbackLocalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfStrictPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumPullbackRescaledMatchesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfRescaledTwistedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsProportionalSeriesMatchTorsioStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationIsoCommInducedLabelMapsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionIsometryValuesIsTorsionLabelSystemStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemTwistByCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSeriesEqUnitMulThetaPointStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ModelData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

/- English proof (translation)
Take `⟨D', hD, hg, hs⟩` from `GlobalTheory.T.exists_pullback_degPre_strict_lineBundle_iso hL O' R f a.D₀ ⊤ (ArcPull.nonempty_psiOn_top _ a.gen) trivial`. Take `⟨th', h₁, h₂⟩` from `GlobalTheory.T.polarisation_generating_section_pullback_local_base hL O' R f a.D₀.P D'.P _ hD.w (pull_grp hD) hD.w_gen A.ν.th A.ν.th_gen`. Take `⟨ν', e₁, e₂⟩` from `GlobalTheory.T.exists_degenerationValues_of_strict_pullback hL.globalFns O' R f a.D₀ D' hD hs C hf A.N A.ν th' h₁ h₂`. Establish `h0 : algebraMap R (FractionRing R) u₀ ≠ 0` using `fun h => u.ne_zero (by rw [hu, h, map_zero])`. Set `q : D'.X → (FractionRing R)ˣ` to `fun y => Units.mk0 _ h0 ^ (a.be (hD.xe y) (hD.xe y) / 2)`.

Take `⟨m, oW, he, w, e, hM, hx, hE, hB⟩` from `GlobalTheory.T.arcDatum_pullback_rescaled_matches hL.globalFns E H D l c O β O' b a R f D' hD u₀ (Units.mk0 _ h0) rfl q _ rfl fun _ => rfl`. Take `⟨νW, e₃, e₄⟩` from `GlobalTheory.T.exists_degenerationValues_of_rescaled_twisted R D' C A.N ν' _ A.be u q fun y => by`. Simplify using `only [q, e₁, A.be_eq, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hu]`. Use `⟨_, m, oW, _, he, w, e, νW, hM, fun y => hD.xe.injective ?_, fun x => ?_, hE, hB, hg⟩` and prove the remaining obligations. Conclude with `((congrArg hD.xe (e₃ y)).trans (e₁ y)).trans (hx _).symm`.

Conclude with `(congrArg (fun t => t.left ≫ PsiEvenPull.proj hD) (e₄ x)).trans (e₂ x)`.
-/
theorem exists_twisted_pull (hL : Laws) [IsLocalRing O'] [IsNoetherianRing O'] (a : ArcIn D l β O' b) {C : Type} [Field C]
    [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) C]
    (f : O' →+* R) (u₀ : R) (hu : (u : C) = algebraMap (FractionRing R) C (algebraMap _ _ u₀))
    (hf : ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) :
    ∃ (DW : DegPre R) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _)
      (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧
      (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ DW.PsiEven ∧ DW.TauBimult ∧ DW.P.g = a.D₀.P.g := by
  obtain ⟨D', hD, hg, hs⟩ := GlobalTheory.T.exists_pullback_degPre_strict_lineBundle_iso hL O' R f a.D₀ ⊤ (ArcPull.nonempty_psiOn_top _ a.gen) trivial
  obtain ⟨th', h₁, h₂⟩ := GlobalTheory.T.polarisation_generating_section_pullback_local_base hL O' R f a.D₀.P D'.P _ hD.w (pull_grp hD) hD.w_gen A.ν.th A.ν.th_gen
  obtain ⟨ν', e₁, e₂⟩ := GlobalTheory.T.exists_degenerationValues_of_strict_pullback hL.globalFns O' R f a.D₀ D' hD hs C hf A.N A.ν th' h₁ h₂
  have h0 : algebraMap R (FractionRing R) u₀ ≠ 0 := fun h => u.ne_zero (by rw [hu, h, map_zero])
  let q : D'.X → (FractionRing R)ˣ := fun y => Units.mk0 _ h0 ^ (a.be (hD.xe y) (hD.xe y) / 2)
  obtain ⟨m, oW, he, w, e, hM, hx, hE, hB⟩ := GlobalTheory.T.arcDatum_pullback_rescaled_matches hL.globalFns E H D l c O β O' b a R f D' hD u₀ (Units.mk0 _ h0) rfl q
    _ rfl fun _ => rfl
  obtain ⟨νW, e₃, e₄⟩ := GlobalTheory.T.exists_degenerationValues_of_rescaled_twisted R D' C A.N ν' _ A.be u q fun y => by
    simp only [q, e₁, A.be_eq, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hu]
  refine ⟨_, m, oW, _, he, w, e, νW, hM, fun y => hD.xe.injective ?_, fun x => ?_, hE, hB, hg⟩
  · exact ((congrArg hD.xe (e₃ y)).trans (e₁ y)).trans (hx _).symm
  · exact (congrArg (fun t => t.left ≫ PsiEvenPull.proj hD) (e₄ x)).trans (e₂ x)

/- English proof (translation)
Use `D.unimod.1 (LinearMap.ext fun y => ?_)` and prove the remaining obligations. Use `congrArg (fun t => D.EF t y) h` as an intermediate fact. Simplify using `only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero, hk.ne', false_or] at this`. Rewrite using `[this, map_zero, LinearMap.zero_apply]`.
-/
theorem eq_zero_of_nsmul (D : Datum H) (k : ℕ) (x : D.La) (hk : 0 < k) (h : k • x = 0) : x = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun t => D.EF t y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hk.ne', false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

/- English proof (translation)
Break down `h with ⟨h, -⟩ | ⟨h, -⟩` into its components or cases. Use `letI := h.toField`. Conclude with `⟨inferInstance, inferInstance⟩`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem local_of_arcBase {ϖ : O'} (h : GlobalTheory.LN.ArcBase O' ϖ) : IsLocalRing O' ∧ IsNoetherianRing O' := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl⟩`.
-/
theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl⟩

/- English proof (translation)
Introduce `hV _ _ _ hT _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO C _ _ _ _ _ _ A u r o M f u₀ hI hr hu1 hu hf n hn ho hn1 hθ`. Use `letI := H.starRing`. Establish `hL : Laws` using `hV.1.1`. Establish `hL2 : Laws2` using `hV.1.2.1`. Take `⟨_, _⟩` from `local_of_arcBase hO`.

Establish `hGt` using `GlobalTheory.T.torus_torsion_points_correspond_values`. Establish `hFam` using `GlobalTheory.T.families_values_correspond hL hL2`. Establish `hWp` using `GlobalTheory.T.torsionPairing_values_of_familiesValues hGt hFam`. Establish `hUth` using `GlobalTheory.T.abelianPartValues_of_expansionLaws hL`. Establish `hUrec` using `GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels (GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values hL hT hUth)`.

Establish `hDvr` using `M.cdv.1`. Establish `hAdm : AdmBase M.W (IsLocalRing.maximalIdeal M.W)` using `⟨inferInstance, inferInstance, inferInstance, M.cdv.2.1⟩`. Establish `hn0 : (n : C) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne_zero`. Establish `hp : ∀ j, 0 < n ^ j` using `fun j => pow_pos hn.pos j`. Establish `xO : CExt O' ⊥ C` using `⟨fun x => hf x ▸ M.ext.1 _, fun x hx => by`.

Rewrite using `[Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]`. Conclude with `one_pos⟩`. Establish `xW : CExt M.W ⊥ C` using `⟨M.ext.1, fun x hx => by`. Rewrite using `[Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]`. Conclude with `one_pos⟩`.

Take `⟨DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hE, hB, hg⟩` from `exists_twisted_pull hL a A u f u₀ hu hf`. Take `⟨S, hS⟩` from `exists_unitBall C`. Take `⟨N', ν', hI'⟩` from `ValuesExist.exists_integral_values hL M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C S fun x => (hS _).2 (M.ext.1 x)`. Establish `hI'' : ν'.IntN` using `⟨S, hS, hI'⟩`. Take `⟨Q', hQ'⟩` from `GlobalTheory.T.degenerationValues_int_of_admissibleBase M.W _ hAdm M.P.D C M.ext N' ν' hI''`.

Take `⟨Q, hQ, -⟩` from `(GlobalTheory.T.arcTorsionValues_norms_integral_positive E H D l Xo c W₀ Y O' b ϖ a hO C xO A hI).2.2 u hu1`. Establish `tN : A.N.toNumB.Tors n a.D₀.P.g` using `GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 hUth O' a.D₀ a.even a.bimult C xO A.N A.ν hI n hn ho hn1`. Establish `tW : (A.N.twist A.be u).toNumB.Tors n DW.P.g` using `hg ▸ tN`. Establish `tN'` using `GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 hUth M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C xW N' ν' hI'' n hn ho hn1`. Take `⟨lA, linA⟩` from `GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q A.hq`.

Establish `ex : ∀ (k : ℕ) (x : D.La), ∃ p : (A.N.twist A.be u).QT k, 0 < k → TwRel A.be u (r k) (A.q k x) p` using `fun k x => by`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `⟨1, fun h => absurd h (lt_irrefl 0)⟩`. Take `⟨p, h, -⟩` from `existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k x)`. Conclude with `⟨p, fun _ => h⟩`.

Use `choose lab hlab using ex`. Establish `lT` using `GlobalTheory.T.torsionLabelSystem_twist_by_compatible_roots C A.N D.La D.EF A.I.ζ A.q _ A.be u r hr lA lab fun k hk x => hlab k x hk`. Take `⟨I', hζ, hTo⟩` from `GlobalTheory.T.exists_torsion_isometry_uniformised_model hV.1 hGt E H D C o M N' ν'`. Establish `G'` using `hGt M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'`. Use `choose lab' hlab' using fun (k : ℕ) (x : D.La) => ((G'.2.2.2.2 k).1 (I'.ev k x)).exists`.

Take `⟨lM, linM⟩` from `GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D M.W M.P.D.toPre M.P.oD M.P.D.psi_even M.P.D.tau_bimult C I' N' ν' lab' hlab'`. Establish `refl' : ∀ k x, QkPt.Equiv _ C (I'.ev k x) (I'.ev k x)` using `fun k x => ((G'.2.2.2.2 k).2.2 _ _ _ _ (hlab' k x) (hlab' k x)).2 ((N'.qEq_equivalence k).refl _)`. Establish `th` using `fun j => GlobalTheory.T.modelSeries_eq_unit_mul_thetaPoint hL (GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt hFam) E H D C o M N' ν' (n ^ j) ho.pow (I'.ev _) (lab' _) _ (fun x z hz => hTo _ (pow_pos (hp j) 2) x _ z (refl' _ x) hz) (hlab' _) ((hθ j).2 (lab _) fun x …`. Establish `h3 : 3 ≤ n ^ 1`. Use `hn.two_le` as an intermediate fact.

Take `⟨t, rfl⟩` from `ho`. Rewrite using `[pow_one]`. Use linear arithmetic over natural numbers and integers. Take `⟨c₀, hc₀, hc⟩` from `GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n ho lT lM (fun j => (th j).1) (Function.ne_iff.1 ((th 1).2 h3))`. Take `⟨mt, hmt⟩` from `GlobalTheory.T.torsionLabelSystems_proportional_series_match_torsion C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn ho (eq_zero_of_nsmul D) lT lM A.I.ζ_pow I'.ζ_pow (fun j => by rw [hζ]; exact (hθ j).1) c₀ hc₀ hc`.

Take `⟨J, hJ, hGeo⟩` from `hUrec M.W DW M.P.D.toPre hE hB M.P.D.psi_even M.P.D.tau_bimult C _ N' νW ν' Q Q' n hn ho hn1 hQ hQ' tW tN' mt`. Establish `hJ'` using `fun j p p' h₁ h₂ => (hmt j p p').1 (hJ j p p' h₁ h₂)`. Use `⟨N', ν', J, fun x y => ?_, fun j x p q' p' z h₁ h₂ h₃ h₄ h₅ => ?_, DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hGeo⟩` and prove the remaining obligations. Establish `key` using `GlobalTheory.T.degenerationIso_comm_induced_label_maps C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn.one_lt lT lM J hJ' (fun j => (GlobalTheory.T.degenerationData_torsion_structure_algClosed C _ n _ hn0 tW j).2.2.1) (A.ν.eX.symm.toAddMonoidHom.comp ((DistribMulAction.toAddMonoidHom _ …`. Take `⟨z, hz⟩` from `linA _ (hp j) x v`.

Use `⟨A.ν.eX.symm z, ?_⟩` and prove the remaining obligations. Rewrite using `[(hlab _ _ (hp j)).1, (hlab _ _ (hp j)).1]`. Conclude with `(A.ν.eX.symm_apply_apply _).symm.trans ((congrArg A.ν.eX.symm hz).trans ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _)))))`. Use the proof step `(fun j v => by`. Take `⟨z, hz⟩` from `linM _ (hp j) x v`.

Conclude with `⟨ν'.eX.symm z, (ν'.eX.symm_apply_apply _).symm.trans ((congrArg ν'.eX.symm hz).trans ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _))))⟩) y`. Conclude with `(congrArg ν'.eX key).trans (ν'.eX.apply_symm_apply _)`. Take `rfl : p = lab _ x` from `(existsUnique_twRel A.be u (r (n ^ j)) (hr.pow (hp j)) (A.q _ x)).unique h₁ (hlab _ x (hp j))`. Take `⟨x₁, a₁, a₂⟩` from `hJ' j _ q' h₂ h₃`. Establish `a₃` using `(lM.2.1 _ (hp j) x₁ x).2 ((lT.2.1 _ (hp j) x₁ x).1 a₁)`.

Establish `E'` using `N'.qEq_equivalence (n ^ j)`. Conclude with `hTo _ (hp j) x p' z (((G'.2.2.2.2 _).2.2 _ _ _ _ (hlab' _ x) h₄).2 (E'.trans (E'.symm a₃) a₂)) h₅`.
-/
theorem data_of_model : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W), A.ν.IntN → Roots u r → ‖(u : C)‖ < 1 → (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → (∀ j, o.I.ζ (n ^ j) = A.I.ζ (n ^ j) ∧ ∀ p : D.La → (A.N.twist A.be u).QT ((n ^ j) ^ 2), (∀ x, TwRel A.be u (r ((n ^ j) ^ 2)) (A.q _ x) (p x)) → o.Theta (n ^ j) fun x => (A.N.twist A.be u).tx (n ^ j) (p x)) → ∃ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'), (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) ∧ (∀ j x (p : (A.N.twist A.be u).QT (n ^ j)) (q' : N'.QT (n ^ j)) p' z, TwRel A.be u (r (n ^ j)) (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev (n ^ j) x).left ≫ M.φ → M.P.ToA C (n ^ j) p' z) ∧ ∃ (DW : DegPre M.W) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _) (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧ (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ GeoIso νW ν' J.toIso := by
  intro hV _ _ _ hT _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO C _ _ _ _ _ _ A u r o M f u₀ hI hr hu1 hu hf n hn ho hn1 hθ
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨_, _⟩ := local_of_arcBase hO
  have hGt := GlobalTheory.T.torus_torsion_points_correspond_values
  have hFam := GlobalTheory.T.families_values_correspond hL hL2
  have hWp := GlobalTheory.T.torsionPairing_values_of_familiesValues hGt hFam
  have hUth := GlobalTheory.T.abelianPartValues_of_expansionLaws hL
  have hUrec := GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels (GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values hL hT hUth)
  have hDvr := M.cdv.1
  have hAdm : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, M.cdv.2.1⟩
  have hn0 : (n : C) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hp : ∀ j, 0 < n ^ j := fun j => pow_pos hn.pos j
  have xO : CExt O' ⊥ C := ⟨fun x => hf x ▸ M.ext.1 _, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  have xW : CExt M.W ⊥ C := ⟨M.ext.1, fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
  obtain ⟨DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hE, hB, hg⟩ := exists_twisted_pull hL a A u f u₀ hu hf
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N', ν', hI'⟩ := ValuesExist.exists_integral_values hL M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C S
    fun x => (hS _).2 (M.ext.1 x)
  have hI'' : ν'.IntN := ⟨S, hS, hI'⟩
  obtain ⟨Q', hQ'⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase M.W _ hAdm M.P.D C M.ext N' ν' hI''
  obtain ⟨Q, hQ, -⟩ := (GlobalTheory.T.arcTorsionValues_norms_integral_positive E H D l Xo c W₀ Y O' b ϖ a hO C xO A hI).2.2 u hu1
  have tN : A.N.toNumB.Tors n a.D₀.P.g := GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 hUth O' a.D₀ a.even a.bimult C xO A.N A.ν hI n hn ho hn1
  have tW : (A.N.twist A.be u).toNumB.Tors n DW.P.g := hg ▸ tN
  have tN' := GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 hUth M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C xW N' ν' hI'' n hn ho hn1

  obtain ⟨lA, linA⟩ := GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D O' a.D₀ a.oa a.even a.bimult C A.I A.N A.ν A.q A.hq
  have ex : ∀ (k : ℕ) (x : D.La), ∃ p : (A.N.twist A.be u).QT k, 0 < k → TwRel A.be u (r k) (A.q k x) p := fun k x => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨p, h, -⟩ := existsUnique_twRel A.be u (r k) (hr.pow hk) (A.q k x)
      exact ⟨p, fun _ => h⟩
  choose lab hlab using ex
  have lT := GlobalTheory.T.torsionLabelSystem_twist_by_compatible_roots C A.N D.La D.EF A.I.ζ A.q _ A.be u r hr lA lab fun k hk x => hlab k x hk

  obtain ⟨I', hζ, hTo⟩ := GlobalTheory.T.exists_torsion_isometry_uniformised_model hV.1 hGt E H D C o M N' ν'
  have G' := hGt M.W M.P.D.toPre M.P.D.psi_even M.P.D.tau_bimult C N' ν'
  choose lab' hlab' using fun (k : ℕ) (x : D.La) => ((G'.2.2.2.2 k).1 (I'.ev k x)).exists
  obtain ⟨lM, linM⟩ := GlobalTheory.T.torsionIsometry_values_isTorsionLabelSystem hGt hWp E H D M.W M.P.D.toPre M.P.oD M.P.D.psi_even M.P.D.tau_bimult C I' N' ν' lab' hlab'
  have refl' : ∀ k x, QkPt.Equiv _ C (I'.ev k x) (I'.ev k x) := fun k x =>
    ((G'.2.2.2.2 k).2.2 _ _ _ _ (hlab' k x) (hlab' k x)).2 ((N'.qEq_equivalence k).refl _)
  have th := fun j => GlobalTheory.T.modelSeries_eq_unit_mul_thetaPoint hL (GlobalTheory.T.theta_constants_eq_degeneration_series hV hGt hFam) E H D C o M N' ν' (n ^ j) ho.pow (I'.ev _) (lab' _) _
    (fun x z hz => hTo _ (pow_pos (hp j) 2) x _ z (refl' _ x) hz) (hlab' _)
    ((hθ j).2 (lab _) fun x => hlab _ x (pow_pos (hp j) 2))
  have h3 : 3 ≤ n ^ 1 := by
    have := hn.two_le
    obtain ⟨t, rfl⟩ := ho
    rw [pow_one]; omega
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n ho lT lM (fun j => (th j).1)
    (Function.ne_iff.1 ((th 1).2 h3))
  obtain ⟨mt, hmt⟩ := GlobalTheory.T.torsionLabelSystems_proportional_series_match_torsion C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn ho (eq_zero_of_nsmul D) lT lM A.I.ζ_pow I'.ζ_pow
    (fun j => by rw [hζ]; exact (hθ j).1) c₀ hc₀ hc
  obtain ⟨J, hJ, hGeo⟩ := hUrec M.W DW M.P.D.toPre hE hB M.P.D.psi_even M.P.D.tau_bimult C _ N' νW ν' Q Q' n hn ho hn1
    hQ hQ' tW tN' mt
  have hJ' := fun j p p' h₁ h₂ => (hmt j p p').1 (hJ j p p' h₁ h₂)
  refine ⟨N', ν', J, fun x y => ?_, fun j x p q' p' z h₁ h₂ h₃ h₄ h₅ => ?_,
    DW, mW, oW, φ, he, w, e, νW, hM, hX, hA, hGeo⟩
  · have key := GlobalTheory.T.degenerationIso_comm_induced_label_maps C _ N' D.La D.EF A.I.ζ I'.ζ lab lab' n hn.one_lt lT lM J hJ'
      (fun j => (GlobalTheory.T.degenerationData_torsion_structure_algClosed C _ n _ hn0 tW j).2.2.1)
      (A.ν.eX.symm.toAddMonoidHom.comp ((DistribMulAction.toAddMonoidHom _ x).comp A.ν.eX.toAddMonoidHom))
      (ν'.eX.symm.toAddMonoidHom.comp ((DistribMulAction.toAddMonoidHom _ x).comp ν'.eX.toAddMonoidHom)) (x • ·)
      (fun j v => by
        obtain ⟨z, hz⟩ := linA _ (hp j) x v
        refine ⟨A.ν.eX.symm z, ?_⟩
        rw [(hlab _ _ (hp j)).1, (hlab _ _ (hp j)).1]
        exact (A.ν.eX.symm_apply_apply _).symm.trans ((congrArg A.ν.eX.symm hz).trans
          ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _)))))
      (fun j v => by
        obtain ⟨z, hz⟩ := linM _ (hp j) x v
        exact ⟨ν'.eX.symm z, (ν'.eX.symm_apply_apply _).symm.trans ((congrArg ν'.eX.symm hz).trans
          ((map_add _ _ _).trans (congrArg _ (map_nsmul _ _ _))))⟩) y
    exact (congrArg ν'.eX key).trans (ν'.eX.apply_symm_apply _)
  · obtain rfl : p = lab _ x :=
      (existsUnique_twRel A.be u (r (n ^ j)) (hr.pow (hp j)) (A.q _ x)).unique h₁ (hlab _ x (hp j))
    obtain ⟨x₁, a₁, a₂⟩ := hJ' j _ q' h₂ h₃
    have a₃ := (lM.2.1 _ (hp j) x₁ x).2 ((lT.2.1 _ (hp j) x₁ x).1 a₁)
    have E' := N'.qEq_equivalence (n ^ j)
    exact hTo _ (hp j) x p' z (((G'.2.2.2.2 _).2.2 _ _ _ _ (hlab' _ x) h₄).2 (E'.trans (E'.symm a₃) a₂)) h₅

end GlobalTheory.ModelData
end
