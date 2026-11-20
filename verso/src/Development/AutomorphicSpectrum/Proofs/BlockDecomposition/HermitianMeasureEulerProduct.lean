import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesNaturalInRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesMeasurePreservingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupportAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixPreservesIntegersAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionInvariantMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityProductBumpsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductNeighbourhoodsShrinkCompactOpenStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

def powT {A ι : Type} [Fintype ι] (t : A → ℂ) (x : ι → A) : ℂ := ∏ i, t (x i)

def fouP {A ι : Type} [CommRing A] [Fintype ι] [MeasurableSpace A] (ψ : AddChar A ℂ) (Bm : Matrix ι ι A)
    (μ : Measure (ι → A)) (Φ : (ι → A) → ℂ) (y : ι → A) : ℂ :=
  ∫ x, Φ x * ψ (dotProduct x (Bm.mulVec y)) ∂μ

/- English proof (translation)
The claim follows from `continuous_finsetProd _ fun i _ => h.comp (continuous_apply i)`.
-/
theorem powT_continuous {A ι : Type} [TopologicalSpace A] [Fintype ι] {t : A → ℂ} (h : Continuous t) :
    Continuous (powT t : (ι → A) → ℂ) :=
  continuous_finsetProd _ fun i _ => h.comp (continuous_apply i)

/- English proof (translation)
Use `HasCompactSupport.intro (K := Set.pi Set.univ fun _ => tsupport t) (isCompact_univ_pi fun _ => h) fun x hx => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ x i ∉ tsupport t := by`. Simplify `hx` using `[Set.mem_pi]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)`.
-/
theorem powT_compact {A ι : Type} [TopologicalSpace A] [T2Space A] [Fintype ι] {t : A → ℂ} (h : HasCompactSupport t) :
    HasCompactSupport (powT t : (ι → A) → ℂ) := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ => tsupport t)
    (isCompact_univ_pi fun _ => h) fun x hx => ?_
  obtain ⟨i, -, hi⟩ : ∃ i, i ∈ Set.univ ∧ x i ∉ tsupport t := by
    simpa [Set.mem_pi] using hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

/- English proof (translation)
Set `φ : AF F →ₐ[F] Fv F v` to `(evalV F v).comp (sndA F)`. Express the relevant statement in the definitionally equal form `φ _ = _`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem eval_mulVec {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (v : HeightOneSpectrum (𝓞 F)) (y : ι → AF F) (i : ι) :
    (sndA F ((B.map (algebraMap F (AF F))).mulVec y i)) v =
      (B.map (algebraMap F (Fv F v))).mulVec (fun j => (sndA F (y j)) v) i := by
  let φ : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)
  change φ _ = _
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

/- English proof (translation)
Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Take `⟨ν, hν⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne F`. Take `⟨S₀, h₀⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx F hF ψ hψ ν hν laminf lam hinf hlam`. Take `⟨S₂, h₂⟩` from `GlobalTheory.T.matrix_preserves_integers_almost_all F ι B hBd`. Use `⟨S₀ ∪ S₂, fun S hS => ?_⟩` and prove the remaining obligations.

Take `⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, hb, hlim⟩` from `h₀ S (Finset.subset_union_left.trans hS)`. Use `haveI : ν.IsAddHaarMeasure := hν.1`. Use `set Bm := B.map (algebraMap F (AF F)) with hBm`. Use `set P : Measure (ι → AF F) := Measure.pi fun _ : ι => ν with hPdef`. Establish `hpres : P.map (fun x => Bm.mulVec x) = P` using `GlobalTheory.T.covolume_one_invariant_under_matrix F ν hν ι B hBd`.

Establish `hu : IsUnit Bm.det` using `GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map _ hBd`. Establish `hemb : MeasurableEmbedding fun x : ι → AF F => Bm.mulVec x` using `(GlobalTheory.CompanionTheory.SW.SdCoord.matE Bm hu).toHomeomorph.measurableEmbedding`. Establish `hT` using `fun k => GlobalTheory.T.fourier_inversion_invariant_matrix (AF F) ν ψ ι Bm (hBs.map _) hemb hpres (testT (ρ k) S (U k)) (fouA ψ ν (testT (ρ k) S (U k))) (fun y => rfl) (hinv k).1 (hinv k).2`. Establish `hc` using `fun k => GlobalTheory.T.continuous_and_hasCompactSupport_testT F (ρ k) S (U k) (hρ k).1 (hρ k).2.1 (fun v => ⟨(hU k v).1, (hU k v).2.1⟩)`. Establish `hfou : ∀ k y, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y = ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i)` using `fun k y => (hT k).1 y`.

Establish `hP : P.IsAddHaarMeasure` using `inferInstance`. Establish `hμP : μ = P`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x, ρ 0 x ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`.

Use `(hρ 0).2.2.2` as an intermediate fact. Simplify using `[hall] at this`. Establish `h0box : (0 : Af F) ∈ boxA S (U 0)` using `⟨fun v _ => (hU 0 v).2.2, fun v _ => zero_mem _⟩`. Use `GlobalTheory.HermSD.eq_of_test_haar hμ hP (powT (testT (ρ 0) S (U 0))) (powT_continuous (hc 0).1) (powT_compact (hc 0).2) ?_ (fun _ => -(pairA F x₀ 0)) ?_ ?_` and prove the remaining obligations. Establish `e : (fun y => ∫ x, powT (testT (ρ 0) S (U 0)) x * ψ (dotProduct x (Bm.mulVec y)) ∂P) = fun y => ∏ i, fouA ψ ν (testT (ρ 0) S (U 0)) (Bm.mulVec y i)` using `funext (hfou 0)`.

Rewrite using `[e]`. Conclude with `(hT 0).2.1`. Use `(integral_congr_ae (ae_of_all _ fun y => ?_)).trans ((hT 0).2.2 _)` and prove the remaining obligations. Conclude with `congrArg (· * _) (hfou 0 y)`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.neg_apply, neg_neg]`. Establish `h1 : testT (ρ 0) S (U 0) (pairA F x₀ 0) = (ρ 0 x₀ : ℂ)`. Establish `: sndA F (pairA F x₀ 0) ∈ boxA S (U 0)` using `h0box`. Simplify using `only [testT, Set.indicator_of_mem this, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Conclude with `hx₀` after adjusting the coercions. Substitute `hμP` using the available equality. Establish `hintP : ∀ k, ∫ x, powT (testT (ρ k) S (U k)) x ∂P = (∫ y, testT (ρ k) S (U k) y ∂ν) ^ Fintype.card ι` using `fun k => by`. Use `integral_fintype_prod_eq_prod (μ := fun _ : ι => ν) (𝕜 := ℂ) (fun _ => testT (ρ k) S (U k))` as an intermediate fact.

Simplify using `only [powT]`. Rewrite using `[this, Finset.prod_const, Finset.card_univ]`. Use `⟨ρ, U, hρ, hρt, hU, hUt, fun k => ⟨powT_continuous (hc k).1, powT_compact (hc k).2⟩, fun k => ?_, fun k => ?_, fun k y => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `e : fouP ψ Bm P (powT (testT (ρ k) S (U k))) = fun y => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i)` using `funext (hfou k)`. Rewrite using `[e]`.

Conclude with `(hT k).2.1`. Rewrite using `[hintP, hint k]`. Rewrite using `[hfou, hintP, norm_pow, norm_prod, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb k _`. Establish `e : ∀ k, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y / ∫ x, powT (testT (ρ k) S (U k)) x ∂P = ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) / ∫ w, testT (ρ k) S (U k) w ∂ν` using `fun k => by`.

Rewrite using `[hfou, hintP, ← Finset.card_univ, ← Finset.prod_const, Finset.prod_div_distrib]`. Simplify using `only [e]`. Establish `hl : Filter.Tendsto (fun k => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) / ∫ w, testT (ρ k) S (U k) w ∂ν) Filter.atTop (nhds (∏ i, (intF S).indicator (fun _ => (1 : ℂ)) (sndA F (Bm.mulVec y i))))` using `tendsto_finsetProd _ fun i _ => hlim _`. Use `hl using 2` and compare the differences between its conclusion and the goal. Establish `hiff : (∀ i, sndA F (Bm.mulVec y i) ∈ intF S) ↔ ∀ i, sndA F (y i) ∈ intF S`.

Establish `hv : ∀ v, v ∉ S → ((∀ i, (sndA F (Bm.mulVec y i)) v ∈ v.adicCompletionIntegers F) ↔ ∀ i, (sndA F (y i)) v ∈ v.adicCompletionIntegers F)` using `fun v hvS => by`. Simplify using `only [hBm, eval_mulVec]`. Conclude with `h₂ v (fun h => hvS (hS (Finset.mem_union_right _ h))) _`. Prove the components needed by the constructor for the conclusion. Introduce `h i v hvS`.

Conclude with `(hv v hvS).1 (fun j => h j v hvS) i`. Introduce `h i v hvS`. Conclude with `(hv v hvS).2 (fun j => h j v hvS) i`. Distinguish the cases in `hy : ∀ i, sndA F (y i) ∈ intF S`. Rewrite using `[Set.indicator_of_mem (by exact hy)]`.

Conclude with `(Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hiff.2 hy i) _).symm`. Rewrite using `[Set.indicator_of_notMem (by exact hy)]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, sndA F (Bm.mulVec y i) ∉ intF S := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hy (hiff.1 h)`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm`.
-/
theorem core (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (hBs : B.IsSymm) (hBd : B.det ≠ 0)
    (μ : Measure (ι → AF F))
    (hμ : SelfDual μ (fun x y => ψ (dotProduct x ((B.map (algebraMap F (AF F))).mulVec y)))) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S →
      ∃ (ρ : ℕ → Ainf F → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)),
        (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧
        Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧
        (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : Fv F v) ∈ U k v) ∧
        (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : Fv F v)).smallSets) ∧
        (∀ k, Continuous (powT (testT (ρ k) S (U k)) : (ι → AF F) → ℂ) ∧
          HasCompactSupport (powT (testT (ρ k) S (U k)) : (ι → AF F) → ℂ)) ∧
        (∀ k, Integrable (fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k)))) μ) ∧
        (∀ k, ∫ x, powT (testT (ρ k) S (U k)) x ∂μ =
          (((∫ y, ρ k y ∂laminf : ℝ) : ℂ) * ∏ v ∈ S, (((lam v) (U k v)).toReal : ℂ)) ^ Fintype.card ι) ∧
        (∀ k y, ‖fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k))) y‖ ≤
          ‖∫ x, powT (testT (ρ k) S (U k)) x ∂μ‖) ∧
        ∀ y, Filter.Tendsto (fun k => fouP ψ (B.map (algebraMap F (AF F))) μ (powT (testT (ρ k) S (U k))) y /
            ∫ x, powT (testT (ρ k) S (U k)) x ∂μ) Filter.atTop
          (nhds ({x : ι → AF F | ∀ i, sndA F (x i) ∈ intF S}.indicator (fun _ => (1 : ℂ)) y)) := by
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne F
  obtain ⟨S₀, h₀⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.exists_test_approx F hF ψ hψ ν hν laminf lam hinf hlam
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.matrix_preserves_integers_almost_all F ι B hBd
  refine ⟨S₀ ∪ S₂, fun S hS => ?_⟩
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, hb, hlim⟩ := h₀ S (Finset.subset_union_left.trans hS)
  haveI : ν.IsAddHaarMeasure := hν.1
  set Bm := B.map (algebraMap F (AF F)) with hBm
  set P : Measure (ι → AF F) := Measure.pi fun _ : ι => ν with hPdef
  have hpres : P.map (fun x => Bm.mulVec x) = P := GlobalTheory.T.covolume_one_invariant_under_matrix F ν hν ι B hBd
  have hu : IsUnit Bm.det := GlobalTheory.CompanionTheory.SW.SdCoord.isUnit_det_map _ hBd
  have hemb : MeasurableEmbedding fun x : ι → AF F => Bm.mulVec x :=
    (GlobalTheory.CompanionTheory.SW.SdCoord.matE Bm hu).toHomeomorph.measurableEmbedding
  have hT := fun k => GlobalTheory.T.fourier_inversion_invariant_matrix (AF F) ν ψ ι Bm (hBs.map _) hemb hpres (testT (ρ k) S (U k))
    (fouA ψ ν (testT (ρ k) S (U k))) (fun y => rfl) (hinv k).1 (hinv k).2
  have hc := fun k => GlobalTheory.T.continuous_and_hasCompactSupport_testT F (ρ k) S (U k) (hρ k).1 (hρ k).2.1 (fun v => ⟨(hU k v).1, (hU k v).2.1⟩)
  have hfou : ∀ k y, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y =
      ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) := fun k y => (hT k).1 y
  have hP : P.IsAddHaarMeasure := inferInstance

  have hμP : μ = P := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, ρ 0 x ≠ 0 := by
      by_contra hall
      push Not at hall
      have := (hρ 0).2.2.2
      simp [hall] at this
    have h0box : (0 : Af F) ∈ boxA S (U 0) :=
      ⟨fun v _ => (hU 0 v).2.2, fun v _ => zero_mem _⟩
    refine GlobalTheory.HermSD.eq_of_test_haar hμ hP (powT (testT (ρ 0) S (U 0)))
      (powT_continuous (hc 0).1) (powT_compact (hc 0).2) ?_ (fun _ => -(pairA F x₀ 0)) ?_ ?_
    · have e : (fun y => ∫ x, powT (testT (ρ 0) S (U 0)) x * ψ (dotProduct x (Bm.mulVec y)) ∂P) =
          fun y => ∏ i, fouA ψ ν (testT (ρ 0) S (U 0)) (Bm.mulVec y i) := funext (hfou 0)
      rw [e]
      exact (hT 0).2.1
    · refine (integral_congr_ae (ae_of_all _ fun y => ?_)).trans ((hT 0).2.2 _)
      exact congrArg (· * _) (hfou 0 y)
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simp only [Pi.neg_apply, neg_neg]
      have h1 : testT (ρ 0) S (U 0) (pairA F x₀ 0) = (ρ 0 x₀ : ℂ) := by
        have : sndA F (pairA F x₀ 0) ∈ boxA S (U 0) := h0box
        simp only [testT, Set.indicator_of_mem this, mul_one]
        rfl
      rw [h1]
      exact_mod_cast hx₀
  subst hμP
  have hintP : ∀ k, ∫ x, powT (testT (ρ k) S (U k)) x ∂P =
      (∫ y, testT (ρ k) S (U k) y ∂ν) ^ Fintype.card ι := fun k => by
    have := integral_fintype_prod_eq_prod (μ := fun _ : ι => ν) (𝕜 := ℂ) (fun _ => testT (ρ k) S (U k))
    simp only [powT]
    rw [this, Finset.prod_const, Finset.card_univ]
  refine ⟨ρ, U, hρ, hρt, hU, hUt, fun k => ⟨powT_continuous (hc k).1, powT_compact (hc k).2⟩, fun k => ?_,
    fun k => ?_, fun k y => ?_, fun y => ?_⟩
  · have e : fouP ψ Bm P (powT (testT (ρ k) S (U k))) =
        fun y => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) := funext (hfou k)
    rw [e]
    exact (hT k).2.1
  · rw [hintP, hint k]
  · rw [hfou, hintP, norm_pow, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hb k _
  · have e : ∀ k, fouP ψ Bm P (powT (testT (ρ k) S (U k))) y / ∫ x, powT (testT (ρ k) S (U k)) x ∂P =
        ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) / ∫ w, testT (ρ k) S (U k) w ∂ν := fun k => by
      rw [hfou, hintP, ← Finset.card_univ, ← Finset.prod_const, Finset.prod_div_distrib]
    simp only [e]
    have hl : Filter.Tendsto (fun k => ∏ i, fouA ψ ν (testT (ρ k) S (U k)) (Bm.mulVec y i) /
        ∫ w, testT (ρ k) S (U k) w ∂ν) Filter.atTop
        (nhds (∏ i, (intF S).indicator (fun _ => (1 : ℂ)) (sndA F (Bm.mulVec y i)))) :=
      tendsto_finsetProd _ fun i _ => hlim _
    convert hl using 2
    have hiff : (∀ i, sndA F (Bm.mulVec y i) ∈ intF S) ↔ ∀ i, sndA F (y i) ∈ intF S := by
      have hv : ∀ v, v ∉ S → ((∀ i, (sndA F (Bm.mulVec y i)) v ∈ v.adicCompletionIntegers F) ↔
          ∀ i, (sndA F (y i)) v ∈ v.adicCompletionIntegers F) := fun v hvS => by
        simp only [hBm, eval_mulVec]
        exact h₂ v (fun h => hvS (hS (Finset.mem_union_right _ h))) _
      constructor
      · intro h i v hvS
        exact (hv v hvS).1 (fun j => h j v hvS) i
      · intro h i v hvS
        exact (hv v hvS).2 (fun j => h j v hvS) i
    by_cases hy : ∀ i, sndA F (y i) ∈ intF S
    · rw [Set.indicator_of_mem (by exact hy)]
      exact (Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hiff.2 hy i) _).symm
    · rw [Set.indicator_of_notMem (by exact hy)]
      obtain ⟨i, hi⟩ : ∃ i, sndA F (Bm.mulVec y i) ∉ intF S := by
        by_contra h
        push Not at h
        exact hy (hiff.1 h)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ (i | ⟨k, p⟩)`. Conclude with `h1 i`. Conclude with `h2 _ _ p.2 k`. Introduce `h`.

Conclude with `⟨fun i => h (Sum.inl i), fun i j hij k => h (Sum.inr (k, ⟨(i, j), hij⟩))⟩`.
-/
theorem mem_latH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (S : HermR (Fv F v) σ n) :
    S ∈ latH σ b v n ↔ ∀ i, hCo (Fv F v) σ b S i ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩ (i | ⟨k, p⟩)
    · exact h1 i
    · exact h2 _ _ p.2 k
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i j hij k => h (Sum.inr (k, ⟨(i, j), hij⟩))⟩

/- English proof (translation)
Rewrite using `[hermV, GlobalTheory.T.hermitian_coordinates_natural_in_ring, hermFin, GlobalTheory.T.hermitian_coordinates_natural_in_ring]`. Both sides reduce to the same expression.
-/
theorem hCo_fin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (AF F) σ n) (i : Idx n d) :
    hCo (Fv F v) σ b (hermV σ v (hermFin σ y)) i = (sndA F (hCo (AF F) σ b y i)) v := by
  rw [hermV, GlobalTheory.T.hermitian_coordinates_natural_in_ring, hermFin, GlobalTheory.T.hermitian_coordinates_natural_in_ring]
  rfl

/- English proof (translation)
Rewrite using `[hermInf, GlobalTheory.T.hermitian_coordinates_natural_in_ring]`.
-/
theorem hCo_inf {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (y : HermR (AF F) σ n) (i : Idx n d) :
    hCo (Ainf F) σ b (hermInf σ y) i = fstA F (hCo (AF F) σ b y i) := by
  rw [hermInf, GlobalTheory.T.hermitian_coordinates_natural_in_ring]

/- English proof (translation)
Establish `hbox : hermFin σ y ∈ boxH σ b n S (fun v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U v)) ↔ ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i`. Use `⟨fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Use `h1 v hv i trivial` as an intermediate fact.

Rewrite `this` using `[hCo_fin]`. Then use the resulting hypothesis. Use `(mem_latH_iff σ b v n _).1 (h2 v hv) i` as an intermediate fact. Rewrite `this` using `[hCo_fin]`. Then use the resulting hypothesis. Introduce `h`. Use `⟨fun v hv i _ => ?_, fun v hv => (mem_latH_iff σ b v n _).2 fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hCo_fin]`. Conclude with `(h i).1 v hv`. Rewrite using `[hCo_fin]`. Conclude with `(h i).2 v hv`. Simplify using `only [testH, powT, testT, Finset.prod_mul_distrib, hCo_inf]`.

Use `push_cast`. Use `congr 1`. Distinguish the cases in `hy : ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U`. Rewrite using `[Set.indicator_of_mem (hbox.2 hy)]`. Conclude with `(Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hy i) _).symm`.

Rewrite `hy` using `[Set.indicator_of_notMem (fun h => hy (hbox.1 h))] push Not`. Take `⟨i, hi⟩` from `hy`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm`.
-/
theorem testH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : HermR (AF F) σ n) :
    testH σ b (fun T => ∏ i, ρ (hCo (Ainf F) σ b T i)) S
        (fun v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U v)) y =
      powT (testT ρ S U) (hCo (AF F) σ b y) := by
  classical
  have hbox : hermFin σ y ∈ boxH σ b n S (fun v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U v)) ↔
      ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U := by
    constructor
    · rintro ⟨h1, h2⟩ i
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := h1 v hv i trivial
        rwa [hCo_fin] at this
      · have := (mem_latH_iff σ b v n _).1 (h2 v hv) i
        rwa [hCo_fin] at this
    · intro h
      refine ⟨fun v hv i _ => ?_, fun v hv => (mem_latH_iff σ b v n _).2 fun i => ?_⟩
      · rw [hCo_fin]
        exact (h i).1 v hv
      · rw [hCo_fin]
        exact (h i).2 v hv
  simp only [testH, powT, testT, Finset.prod_mul_distrib, hCo_inf]
  push_cast
  congr 1
  by_cases hy : ∀ i, sndA F (hCo (AF F) σ b y i) ∈ boxA S U
  · rw [Set.indicator_of_mem (hbox.2 hy)]
    exact (Finset.prod_eq_one fun i _ => Set.indicator_of_mem (hy i) _).symm
  · rw [Set.indicator_of_notMem (fun h => hy (hbox.1 h))]
    push Not at hy
    obtain ⟨i, hi⟩ := hy
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i v hv`. Use `(mem_latH_iff σ b v n _).1 (h v hv) i` as an intermediate fact. Rewrite `this` using `[hCo_fin]`. Then use the resulting hypothesis. Introduce `h v hv`.

Use `(mem_latH_iff σ b v n _).2 fun i => ?_` and prove the remaining obligations. Rewrite using `[hCo_fin]`. Conclude with `h i v hv`.
-/
theorem mem_intH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F))) (y : HermR (AF F) σ n) :
    hermFin σ y ∈ intH σ b n S ↔ ∀ i, sndA F (hCo (AF F) σ b y i) ∈ intF S := by
  constructor
  · intro h i v hv
    have := (mem_latH_iff σ b v n _).1 (h v hv) i
    rwa [hCo_fin] at this
  · intro h v hv
    refine (mem_latH_iff σ b v n _).2 fun i => ?_
    rw [hCo_fin]
    exact h i v hv

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT fouA intF boxA)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ db hdb d b laminf lam hinf hlam`. Establish `hF` using `hCM.1`. Take `⟨t1, -, -, -, -, -, -, -, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)`. Use `haveI := t1`. Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`.

Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩`. Use `haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩`. Use `haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩`.

Take `⟨a1, a2, a3, a4, -, -, -, -⟩` from `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF`. Use `haveI := a1`. Use `haveI := a2`. Use `haveI := a3`. Use `haveI := a4`.

Establish `hloc` using `fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v) := fun v => (hloc v).2.2.2.1`.

Use `haveI : laminf.IsAddHaarMeasure := hinf.1`. Use `haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1`. Take `⟨eA, heA⟩` from `GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (AF F) d b n`. Take `⟨eI, heI⟩` from `GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Ainf F) d b n`. Use `choose eV heV using fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Fv F v) d b n`.

Take `⟨hBs, hBd⟩` from `GlobalTheory.T.coordinate_form_symmetric_nondegenerate F E σ hCM d b n`. Use `set B := coordForm σ b n with hB`. Use `set Bm := B.map (algebraMap F (AF F)) with hBm`. Establish `hpair : ∀ w y : HermR (AF F) σ n, pairHerm (AF F) σ n w y = dotProduct (eA w) (Bm.mulVec (eA y))`. Introduce `w y`.

Rewrite using `[heA, heA]`. Conclude with `GlobalTheory.T.hermitian_pairing_in_coordinates F E σ hCM (AF F) d b n w y`. Establish `hdb' : SelfDual db (fun S T => ψ (pairHerm (AF F) σ n S T))` using `hdb`. Establish `hsd : SelfDual (db.map eA) (fun x y => ψ (dotProduct x (Bm.mulVec y)))`. Establish `h` using `GlobalTheory.CompanionTheory.SW.SdAny.selfDual_map eA db _ hdb'`.

Simplify using `only [hpair, ContinuousAddEquiv.apply_symm_apply] at h`. Conclude with `h`. Establish `hemb : MeasurableEmbedding eA` using `eA.toHomeomorph.measurableEmbedding`. Take `⟨S₁, hcore⟩` from `core F hF ψ hψ laminf lam hinf hlam (Idx n d) B hBs hBd (db.map eA) hsd`. Use `⟨S₁, fun S hS => ?_⟩` and prove the remaining obligations.

Take `⟨ρ, U, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩` from `hcore S hS`. Establish `hcoI : ∀ T, hCo (Ainf F) σ b T = eI T` using `fun T => (heI T).symm`. Establish `hcoV : ∀ v T, hCo (Fv F v) σ b T = eV v T` using `fun v T => (heV v T).symm`. Take `⟨g1, g2⟩` from `GlobalTheory.T.approximate_identity_product_bumps (HermR (Ainf F) σ n) (Ainf F) (Idx n d) eI ρ (fun k => ⟨(h1 k).1, (h1 k).2.1, (h1 k).2.2.1⟩) h2`. Establish `g3` using `fun v => GlobalTheory.T.product_neighbourhoods_shrink_compact_open (HermR (Fv F v) σ n) (Fv F v) (Idx n d) (eV v) (fun k => U k v) (fun k => h3 k v) (h4 v)`.

Establish `hρe : ∀ k, (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i)) = fun T => ∏ i, ρ k (eI T i)` using `fun k => by`. Use function extensionality and compare the values at `T`. Rewrite using `[hcoI]`. Establish `hUe : ∀ k v, hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) = eV v ⁻¹' Set.pi Set.univ (fun _ => U k v)` using `fun k v => by`. Use extensionality with `T`.

Simplify using `only [Set.mem_preimage, hcoV]`. Use `set ρh : ℕ → HermR (Ainf F) σ n → ℝ := fun k T => ∏ i, ρ k (hCo (Ainf F) σ b T i) with hρh`. Use `set Uh : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n) := fun k v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) with hUh`. Establish `hτ : ∀ k, testH σ b (ρh k) S (Uh k) = fun y => powT (testT (ρ k) S (U k)) (eA y)` using `fun k => by`. Use function extensionality and compare the values at `y`.

Rewrite using `[heA]`. Conclude with `testH_eq σ b (ρ k) S (U k) y`. Establish `hf : ∀ k, fouH σ ψ db (testH σ b (ρh k) S (Uh k)) = fun y => fouP ψ Bm (db.map eA) (powT (testT (ρ k) S (U k))) (eA y)` using `fun k => by`. Use function extensionality and compare the values at `y`. Simplify using `only [fouH, fouP]`.

Rewrite using `[hemb.integral_map]`. Use `integral_congr_ae (ae_of_all _ fun w => ?_)` and prove the remaining obligations. Simplify using `only [hτ, hpair]`. Establish `hI : ∀ k, ∫ w, testH σ b (ρh k) S (Uh k) w ∂db = ∫ x, powT (testT (ρ k) S (U k)) x ∂(db.map eA)` using `fun k => by`. Rewrite using `[hemb.integral_map, hτ]`.

Establish `hmI : (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI = Measure.pi fun _ : Idx n d => laminf`. Rewrite using `[← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Ainf F) d b laminf hinf.1 n]`. Use `congr 1`. Use function extensionality and compare the values at `T`. Conclude with `(heI T)`.

Establish `hmV : ∀ v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n).map (eV v) = Measure.pi fun _ : Idx n d => lam v` using `fun v => by`. Rewrite using `[← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Fv F v) d b (lam v) (hlam v).1 n]`. Use `congr 1`. Use function extensionality and compare the values at `T`. Conclude with `(heV v T)`.

Establish `hembI : MeasurableEmbedding eI` using `eI.toHomeomorph.measurableEmbedding`. Establish `hembV : ∀ v, MeasurableEmbedding (eV v)` using `fun v => (eV v).toHomeomorph.measurableEmbedding`. Establish `hρI : ∀ k, ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) = (∫ y, ρ k y ∂laminf) ^ Fintype.card (Idx n d)` using `fun k => by`. Establish `e1 : ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) = ∫ x, ∏ i, ρ k (x i) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI)`. Use `Eq.trans ?_ (hembI.integral_map (μ := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) (fun x => ∏ i, ρ k (x i))).symm` and prove the remaining obligations.

Conclude with `integral_congr_ae (ae_of_all _ fun T => by simp only [hρh, hcoI])`. Rewrite using `[e1, hmI, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ => ρ k), Finset.prod_const, Finset.card_univ]`. Establish `hUV : ∀ k v, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v) = (lam v (U k v)) ^ Fintype.card (Idx n d)` using `fun k v => by`. Establish `e1 : Uh k v = eV v ⁻¹' Set.pi Set.univ (fun _ => U k v)` using `hUe k v`. Rewrite using `[e1]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hmV, Measure.pi_pi, Finset.prod_const, Finset.card_univ]`. Establish `hUpos : ∀ k v, 0 < lam v (U k v)` using `fun k v => (h3 k v).2.1.measure_pos (lam v) ⟨0, (h3 k v).2.2⟩`. Establish `hUfin : ∀ k v, lam v (U k v) ≠ ⊤` using `fun k v => (h3 k v).1.measure_lt_top.ne`. Establish `hUr : ∀ k v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v)).toReal = (lam v (U k v)).toReal ^ Fintype.card (Idx n d)` using `fun k v => by`.

Rewrite using `[hUV, ENNReal.toReal_pow]`. Establish `hcont : ∀ k, Continuous (testH σ b (ρh k) S (Uh k))` using `fun k => by`. Rewrite using `[hτ]`. Conclude with `(h5 k).1.comp eA.continuous`. Establish `hcs : ∀ k, HasCompactSupport (testH σ b (ρh k) S (Uh k))` using `fun k => by`.

Rewrite using `[hτ]`. Conclude with `(h5 k).2.comp_homeomorph eA.toHomeomorph`. Establish `hint : ∀ k, Integrable (fouH σ ψ db (testH σ b (ρh k) S (Uh k))) db` using `fun k => by`. Rewrite using `[hf]`. Conclude with `(hemb.integrable_map_iff).1 (h6 k)`.

Use `⟨ρh, Uh, fun k => ?_, ?_, fun k v => ?_, fun v => ?_, fun k => ⟨hint k, fun z => ?_⟩, fun k => ?_, fun k y => ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `e` using `hρe k`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))`. Rewrite using `[e]`.

Conclude with `(g1 k).1`. Express the relevant statement in the definitionally equal form `HasCompactSupport (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))`. Rewrite using `[e]`. Conclude with `(g1 k).2.1`. Introduce `T`.

Conclude with `Finset.prod_nonneg fun i _ => (h1 k).2.2.1 _`. Rewrite using `[hρI]`. Conclude with `pow_pos (h1 k).2.2.2 _`. Establish `e : (fun k => tsupport (ρh k)) = fun k => tsupport (fun T => ∏ i, ρ k (eI T i))`. Use function extensionality and compare the values at `k`.

Conclude with `congrArg tsupport (hρe k)`. Rewrite using `[e]`. Conclude with `g2`. Establish `e` using `hUe k v`. Take `⟨c1, c2, c3⟩` from `(g3 v).1 k`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsCompact (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))`. Rewrite using `[e]`. Conclude with `c1`. Express the relevant statement in the definitionally equal form `IsOpen (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))`.

Rewrite using `[e]`. Conclude with `c2`. Express the relevant statement in the definitionally equal form `(0 : HermR (Fv F v) σ n) ∈ hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v)`. Rewrite using `[e]`. Conclude with `c3`.

Rewrite using `[hUr]`. Conclude with `pow_pos (ENNReal.toReal_pos (hUpos k v).ne' (hUfin k v)) _`. Establish `e : (fun k => Uh k v) = fun k => eV v ⁻¹' Set.pi Set.univ (fun _ => U k v)` using `funext fun k => hUe k v`. Rewrite using `[e]`. Conclude with `(g3 v).2`.

Conclude with `hdb'.2 _ (hcont k) (hcs k) (hint k) z`. Rewrite using `[hI, h7, hρI, mul_pow]`. Use `congr 1`. Use `push_cast`. Both sides reduce to the same expression.

Simplify using `only [hUr]`. Use `push_cast`. Rewrite using `[Finset.prod_pow]`. Rewrite using `[hf, hI]`. Conclude with `h8 k _`.

Establish `hlim` using `h9 (eA y)`. Simplify using `only [hf, hI]`. Establish `e : (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) = {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S}.indicator (fun _ => (1 : ℂ)) (eA y)`. Distinguish the cases in `hy : hermFin σ y ∈ intH σ b n S`. Establish `h' : eA y ∈ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S}`.

Use `(mem_intH_iff σ b S y).1 hy` as an intermediate fact. Rewrite `this` using `[← heA]`. Then use the resulting hypothesis. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem h']`. Establish `h' : eA y ∉ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S}`. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Use `(mem_intH_iff σ b S y).2 ?_` and prove the remaining obligations. Rewrite using `[← heA]` and apply the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem h']`. Rewrite using `[e]`.

Conclude with `hlim`.
-/
theorem exists_testH_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v ∧ 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k, Integrable (fouH σ ψ db (testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, fouH σ ψ db (testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖fouH σ ψ db (testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ w, testH σ b (ρ k) S (U k) w ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => fouH σ ψ db (testH σ b (ρ k) S (U k)) y / ∫ w, testH σ b (ρ k) S (U k) w ∂db) Filter.atTop (nhds ((intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ db hdb d b laminf lam hinf hlam
  classical
  have hF := hCM.1
  obtain ⟨t1, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := t1
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (HermR (Fv F v) σ n) := fun v => ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := a1; haveI := a2; haveI := a3; haveI := a4
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v) := fun v => (hloc v).2.2.2.1
  haveI : laminf.IsAddHaarMeasure := hinf.1
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (AF F) d b n
  obtain ⟨eI, heI⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Ainf F) d b n
  choose eV heV using fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.T.exists_homeomorph_hermR_coordinates F E σ hCM (Fv F v) d b n
  obtain ⟨hBs, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate F E σ hCM d b n
  set B := coordForm σ b n with hB
  set Bm := B.map (algebraMap F (AF F)) with hBm
  have hpair : ∀ w y : HermR (AF F) σ n, pairHerm (AF F) σ n w y = dotProduct (eA w) (Bm.mulVec (eA y)) := by
    intro w y
    rw [heA, heA]
    exact GlobalTheory.T.hermitian_pairing_in_coordinates F E σ hCM (AF F) d b n w y
  have hdb' : SelfDual db (fun S T => ψ (pairHerm (AF F) σ n S T)) := hdb
  have hsd : SelfDual (db.map eA) (fun x y => ψ (dotProduct x (Bm.mulVec y))) := by
    have h := GlobalTheory.CompanionTheory.SW.SdAny.selfDual_map eA db _ hdb'
    simp only [hpair, ContinuousAddEquiv.apply_symm_apply] at h
    exact h
  have hemb : MeasurableEmbedding eA := eA.toHomeomorph.measurableEmbedding
  obtain ⟨S₁, hcore⟩ := core F hF ψ hψ laminf lam hinf hlam (Idx n d) B hBs hBd (db.map eA) hsd
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hcore S hS
  have hcoI : ∀ T, hCo (Ainf F) σ b T = eI T := fun T => (heI T).symm
  have hcoV : ∀ v T, hCo (Fv F v) σ b T = eV v T := fun v T => (heV v T).symm
  obtain ⟨g1, g2⟩ := GlobalTheory.T.approximate_identity_product_bumps (HermR (Ainf F) σ n) (Ainf F) (Idx n d) eI ρ
    (fun k => ⟨(h1 k).1, (h1 k).2.1, (h1 k).2.2.1⟩) h2
  have g3 := fun v => GlobalTheory.T.product_neighbourhoods_shrink_compact_open (HermR (Fv F v) σ n) (Fv F v) (Idx n d) (eV v) (fun k => U k v)
    (fun k => h3 k v) (h4 v)
  have hρe : ∀ k, (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i)) = fun T => ∏ i, ρ k (eI T i) := fun k => by
    funext T
    rw [hcoI]
  have hUe : ∀ k v, hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) =
      eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := fun k v => by
    ext T
    simp only [Set.mem_preimage, hcoV]
  set ρh : ℕ → HermR (Ainf F) σ n → ℝ := fun k T => ∏ i, ρ k (hCo (Ainf F) σ b T i) with hρh
  set Uh : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n) :=
    fun k v => hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v) with hUh
  have hτ : ∀ k, testH σ b (ρh k) S (Uh k) = fun y => powT (testT (ρ k) S (U k)) (eA y) := fun k => by
    funext y
    rw [heA]
    exact testH_eq σ b (ρ k) S (U k) y
  have hf : ∀ k, fouH σ ψ db (testH σ b (ρh k) S (Uh k)) =
      fun y => fouP ψ Bm (db.map eA) (powT (testT (ρ k) S (U k))) (eA y) := fun k => by
    funext y
    simp only [fouH, fouP]
    rw [hemb.integral_map]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [hτ, hpair]
  have hI : ∀ k, ∫ w, testH σ b (ρh k) S (Uh k) w ∂db = ∫ x, powT (testT (ρ k) S (U k)) x ∂(db.map eA) := fun k => by
    rw [hemb.integral_map, hτ]
  have hmI : (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI = Measure.pi fun _ : Idx n d => laminf := by
    rw [← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Ainf F) d b laminf hinf.1 n]
    congr 1
    funext T
    exact (heI T)
  have hmV : ∀ v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n).map (eV v) = Measure.pi fun _ : Idx n d => lam v := fun v => by
    rw [← GlobalTheory.T.hermitian_coordinates_measure_preserving F E σ hCM (Fv F v) d b (lam v) (hlam v).1 n]
    congr 1
    funext T
    exact (heV v T)
  have hembI : MeasurableEmbedding eI := eI.toHomeomorph.measurableEmbedding
  have hembV : ∀ v, MeasurableEmbedding (eV v) := fun v => (eV v).toHomeomorph.measurableEmbedding
  have hρI : ∀ k, ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) =
      (∫ y, ρ k y ∂laminf) ^ Fintype.card (Idx n d) := fun k => by
    have e1 : ∫ y, ρh k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) =
        ∫ x, ∏ i, ρ k (x i) ∂((GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n).map eI) := by
      refine Eq.trans ?_ (hembI.integral_map (μ := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)
        (fun x => ∏ i, ρ k (x i))).symm
      exact integral_congr_ae (ae_of_all _ fun T => by simp only [hρh, hcoI])
    rw [e1, hmI, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ => ρ k), Finset.prod_const, Finset.card_univ]
  have hUV : ∀ k v, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v) =
      (lam v (U k v)) ^ Fintype.card (Idx n d) := fun k v => by
    have e1 : Uh k v = eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := hUe k v
    rw [e1]
    calc GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (eV v ⁻¹' Set.pi Set.univ (fun _ => U k v))
        = ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n).map (eV v)) (Set.pi Set.univ (fun _ => U k v)) :=
          ((hembV v).map_apply (μ := GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) _).symm
      _ = (lam v (U k v)) ^ Fintype.card (Idx n d) := by
          rw [hmV, Measure.pi_pi, Finset.prod_const, Finset.card_univ]
  have hUpos : ∀ k v, 0 < lam v (U k v) := fun k v =>
    (h3 k v).2.1.measure_pos (lam v) ⟨0, (h3 k v).2.2⟩
  have hUfin : ∀ k v, lam v (U k v) ≠ ⊤ := fun k v => (h3 k v).1.measure_lt_top.ne
  have hUr : ∀ k v, (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (Uh k v)).toReal =
      (lam v (U k v)).toReal ^ Fintype.card (Idx n d) := fun k v => by
    rw [hUV, ENNReal.toReal_pow]
  have hcont : ∀ k, Continuous (testH σ b (ρh k) S (Uh k)) := fun k => by
    rw [hτ]
    exact (h5 k).1.comp eA.continuous
  have hcs : ∀ k, HasCompactSupport (testH σ b (ρh k) S (Uh k)) := fun k => by
    rw [hτ]
    exact (h5 k).2.comp_homeomorph eA.toHomeomorph
  have hint : ∀ k, Integrable (fouH σ ψ db (testH σ b (ρh k) S (Uh k))) db := fun k => by
    rw [hf]
    exact (hemb.integrable_map_iff).1 (h6 k)
  refine ⟨ρh, Uh, fun k => ?_, ?_, fun k v => ?_, fun v => ?_, fun k => ⟨hint k, fun z => ?_⟩, fun k => ?_,
    fun k y => ?_, fun y => ?_⟩
  · have e := hρe k
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Continuous (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))
      rw [e]
      exact (g1 k).1
    · change HasCompactSupport (fun T => ∏ i, ρ k (hCo (Ainf F) σ b T i))
      rw [e]
      exact (g1 k).2.1
    · intro T
      exact Finset.prod_nonneg fun i _ => (h1 k).2.2.1 _
    · rw [hρI]
      exact pow_pos (h1 k).2.2.2 _
  · have e : (fun k => tsupport (ρh k)) = fun k => tsupport (fun T => ∏ i, ρ k (eI T i)) := by
      funext k
      exact congrArg tsupport (hρe k)
    rw [e]
    exact g2
  · have e := hUe k v
    obtain ⟨c1, c2, c3⟩ := (g3 v).1 k
    refine ⟨?_, ?_, ?_, ?_⟩
    · change IsCompact (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))
      rw [e]
      exact c1
    · change IsOpen (hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v))
      rw [e]
      exact c2
    · change (0 : HermR (Fv F v) σ n) ∈ hCo (Fv F v) σ b ⁻¹' Set.pi Set.univ (fun _ => U k v)
      rw [e]
      exact c3
    · rw [hUr]
      exact pow_pos (ENNReal.toReal_pos (hUpos k v).ne' (hUfin k v)) _
  · have e : (fun k => Uh k v) = fun k => eV v ⁻¹' Set.pi Set.univ (fun _ => U k v) := funext fun k => hUe k v
    rw [e]
    exact (g3 v).2
  · exact hdb'.2 _ (hcont k) (hcs k) (hint k) z
  · rw [hI, h7, hρI, mul_pow]
    congr 1
    · push_cast
      rfl
    · simp only [hUr]
      push_cast
      rw [Finset.prod_pow]
  · rw [hf, hI]
    exact h8 k _
  · have hlim := h9 (eA y)
    simp only [hf, hI]
    have e : (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) =
        {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S}.indicator (fun _ => (1 : ℂ)) (eA y) := by
      by_cases hy : hermFin σ y ∈ intH σ b n S
      · have h' : eA y ∈ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S} := by
          have := (mem_intH_iff σ b S y).1 hy
          rwa [← heA] at this
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem h']
      · have h' : eA y ∉ {x : Idx n d → AF F | ∀ i, sndA F (x i) ∈ intF S} := by
          intro h
          apply hy
          refine (mem_intH_iff σ b S y).2 ?_
          rwa [← heA]
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem h']
    rw [e]
    exact hlim

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
