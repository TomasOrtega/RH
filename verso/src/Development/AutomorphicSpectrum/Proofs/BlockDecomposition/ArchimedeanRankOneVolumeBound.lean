import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruenceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticLevelSetDensityStatement
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanCoordinateMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuplesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanLocalDensityFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.InfTransport

section SlopeTestRemainingChoices

def swapHomeo {A ι P : Type} [TopologicalSpace A] (eH : A ≃ₜ (P → ℝ)) : (ι → A) ≃ₜ (P → ι → ℝ) where
  toFun z w p := eH (z p) w
  invFun y p := eH.symm (fun w => y w p)
  left_inv z := by funext p; simp
  right_inv y := by funext w p; simp
  continuous_toFun := continuous_pi fun w => continuous_pi fun p =>
    (continuous_apply w).comp (eH.continuous.comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => eH.symm.continuous.comp
    (continuous_pi fun w => (continuous_apply p).comp (continuous_apply w))

/- English proof (translation)
Establish `h : (coreR δ R : Set (P → ι → ℝ)) = ⋂ w, {x | δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}`. Use extensionality with `x`. Simplify using `[coreR]`. Rewrite using `[h]`. Conclude with `isClosed_iInter fun w => (isClosed_le continuous_const (continuous_apply w).norm).inter (isClosed_le (continuous_apply w).norm continuous_const)`.
-/
theorem isClosed_coreR {P ι : Type} [Fintype P] [Fintype ι] (δ R : ℝ) :
    IsClosed (coreR δ R : Set (P → ι → ℝ)) := by
  have h : (coreR δ R : Set (P → ι → ℝ)) = ⋂ w, {x | δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R} := by
    ext x
    simp [coreR]
  rw [h]
  exact isClosed_iInter fun w =>
    (isClosed_le continuous_const (continuous_apply w).norm).inter
      (isClosed_le (continuous_apply w).norm continuous_const)

/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded (isClosed_coreR δ R) ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (0 : P → ι → ℝ)) (r := R)).subset fun x hx => ?_` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `(pi_norm_le_iff_of_nonneg hR.le).2 fun w => (hx w).2`.
-/
theorem isCompact_coreR {P ι : Type} [Fintype P] [Fintype ι] (δ : ℝ) {R : ℝ} (hR : 0 < R) :
    IsCompact (coreR δ R : Set (P → ι → ℝ)) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_coreR δ R) ?_
  refine (Metric.isBounded_closedBall (x := (0 : P → ι → ℝ)) (r := R)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hR.le).2 fun w => (hx w).2

/- English proof (translation)
Establish `hc₂' : (0 : ℝ) < c₂` using `NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc₂)`. Establish `hc₁ : (0 : ℝ) ≤ c₁` using `c₁.coe_nonneg`. Establish `ha : 0 ≤ (c₁ : ℝ) * K` using `mul_nonneg hc₁ hK`. Establish `ht : 0 < ε * ((c₂ : ℝ) * κ)` using `by positivity`. Use `⟨ε * ((c₂ : ℝ) * κ) / ((c₁ : ℝ) * K + 1), by positivity, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂'.le, ← ENNReal.ofReal_mul hε.le]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1 : (c₁ : ℝ) * (K * (ε * ((c₂ : ℝ) * κ) / ((c₁ : ℝ) * K + 1))) = ((c₁ : ℝ) * K) * (ε * ((c₂ : ℝ) * κ)) / ((c₁ : ℝ) * K + 1)` using `by ring`. Rewrite using `[h1, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_small_const (c₁ c₂ : ℝ≥0) (hc₂ : c₂ ≠ 0) {κ K ε : ℝ} (hκ : 0 < κ) (hK : 0 ≤ K)
    (hε : 0 < ε) : ∃ ε' : ℝ, 0 < ε' ∧
      (c₁ : ℝ≥0∞) * (ENNReal.ofReal K * ENNReal.ofReal ε') ≤
        ENNReal.ofReal ε * ((c₂ : ℝ≥0∞) * ENNReal.ofReal κ) := by
  have hc₂' : (0 : ℝ) < c₂ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc₂)
  have hc₁ : (0 : ℝ) ≤ c₁ := c₁.coe_nonneg
  have ha : 0 ≤ (c₁ : ℝ) * K := mul_nonneg hc₁ hK
  have ht : 0 < ε * ((c₂ : ℝ) * κ) := by positivity
  refine ⟨ε * ((c₂ : ℝ) * κ) / ((c₁ : ℝ) * K + 1), by positivity, ?_⟩
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂'.le,
    ← ENNReal.ofReal_mul hε.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (c₁ : ℝ) * (K * (ε * ((c₂ : ℝ) * κ) / ((c₁ : ℝ) * K + 1))) =
      ((c₁ : ℝ) * K) * (ε * ((c₂ : ℝ) * κ)) / ((c₁ : ℝ) * K + 1) := by ring
  rw [h1, div_le_iff₀ (by positivity)]
  nlinarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `h1 : ∀ w, ‖xw e b X w‖ ≤ ∑ p : Fin M × Fin d, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖`. Introduce `w`. Use `(pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun p => ?_` and prove the remaining obligations. Establish `h2 : ‖xw e b X w p‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖`. Rewrite using `[Real.norm_eq_abs]`.

Conclude with `hen _ w`. Rewrite using `[h2]`. Conclude with `Finset.single_le_sum (f := fun p : Fin M × Fin d => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p)`. Use `(Finset.sum_le_sum fun w _ => h1 w).trans (le_of_eq ?_)` and prove the remaining obligations. Unfold `sizeTup sizeInf`.

Rewrite using `[Finset.sum_comm, Fintype.sum_prod_type]`. Simplify using the standard rewrite rules.
-/
theorem sum_norm_xw_le {M d : ℕ} (b : Module.Basis (Fin d) F E)
    (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (hen : ∀ y w, |e y w| = ‖y w‖)
    (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    ∑ w, ‖xw e b X w‖ ≤ sizeTup b X := by
  have h1 : ∀ w, ‖xw e b X w‖ ≤ ∑ p : Fin M × Fin d,
      ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖ := by
    intro w
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun p => ?_
    have h2 : ‖xw e b X w p‖ = ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖ := by
      rw [Real.norm_eq_abs]
      exact hen _ w
    rw [h2]
    exact Finset.single_le_sum
      (f := fun p : Fin M × Fin d => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr (X 0 p.1) p.2 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
  refine (Finset.sum_le_sum fun w _ => h1 w).trans (le_of_eq ?_)
  unfold sizeTup sizeInf
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  simp

/- English proof (translation)
Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`. Use `haveI := i4`.

Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Set `eH : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `he.homeomorph e`. Set `eA : (InfinitePlace F → ℝ) ≃+ Ainf F` to `(e : Ainf F ≃+ (InfinitePlace F → ℝ)).symm`. Establish `hAc : Continuous eA`. Establish `h0 : (eA : _ → _) = eH.symm` using `funext fun y => eH.injective (by`.

Rewrite using `[eH.apply_symm_apply]`. Conclude with `e.apply_symm_apply y)`. Rewrite using `[h0]`. Conclude with `eH.symm.continuous`. Use `haveI h1 : ((volume : Measure (InfinitePlace F → ℝ)).map eA).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map _ eA hAc he.continuous`.

Use `⟨ENNReal.ofReal κ • (volume : Measure (InfinitePlace F → ℝ)).map eA, Measure.IsAddHaarMeasure.smul _ (by simpa using hκ) ENNReal.ofReal_ne_top, ?_⟩` and prove the remaining obligations. Establish `h2 : (e : Ainf F → _) ∘ eA = id`. Use function extensionality and compare the values at `y`. Conclude with `e.apply_symm_apply y`. Rewrite using `[Measure.map_smul, Measure.map_map he.continuous.measurable hAc.measurable, h2, Measure.map_id]`.
-/
theorem exists_haar_map (hF : IsTotallyReal F) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : IsHomeomorph e) {κ : ℝ} (hκ : 0 < κ) :
    ∃ lam : Measure (Ainf F), lam.IsAddHaarMeasure ∧
      lam.map e = ENNReal.ofReal κ • (volume : Measure (InfinitePlace F → ℝ)) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hF
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let eA : (InfinitePlace F → ℝ) ≃+ Ainf F := (e : Ainf F ≃+ (InfinitePlace F → ℝ)).symm
  have hAc : Continuous eA := by
    have h0 : (eA : _ → _) = eH.symm := funext fun y => eH.injective (by
      rw [eH.apply_symm_apply]
      exact e.apply_symm_apply y)
    rw [h0]
    exact eH.symm.continuous
  haveI h1 : ((volume : Measure (InfinitePlace F → ℝ)).map eA).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ eA hAc he.continuous
  refine ⟨ENNReal.ofReal κ • (volume : Measure (InfinitePlace F → ℝ)).map eA,
    Measure.IsAddHaarMeasure.smul _ (by simpa using hκ) ENNReal.ofReal_ne_top, ?_⟩
  have h2 : (e : Ainf F → _) ∘ eA = id := by
    funext y
    exact e.apply_symm_apply y
  rw [Measure.map_smul, Measure.map_map he.continuous.measurable hAc.measurable, h2, Measure.map_id]

end SlopeTestRemainingChoices

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ hM d b ρ e hρ he heρ hen hreal μ ν hμ hν φ hφc hφ0 hφR ε hε`. Take `⟨i1, i2, i3, i4, -⟩` from `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI := i3`.

Use `haveI := i4`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩`. Take `⟨t1, t2, t3, t4, -, -, -, t8, t9, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)`. Use `haveI := t1`.

Use `haveI := t2`. Use `haveI := t3`. Use `haveI := t4`. Use `haveI := t8 1 M`. Use `haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) := inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → Ainf F ⊗[F] E))`.

Use `haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) := inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ainf F ⊗[F] E))`. Use `haveI : LocallyCompactSpace (HermR (Ainf F) σ 1) := (t9 1).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (HermR (Ainf F) σ 1) := TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hd : d = 2`. Establish `h1` using `Module.finrank_eq_card_basis b`.

Rewrite `h1` using `[hcm.2.2.1]`. Simplify using `using h1.symm`. Establish `hs : ∀ x, σ (σ x) = x` using `HermOne.sig_sig hcm`. Take `⟨B, hBs, hBd, -, hBR⟩` from `GlobalTheory.T.exists_trace_form_gram_matrix_in_basis F E σ hcm M J hJ d b`. Establish `hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ, P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w)`.

Introduce `w`. Use `GlobalTheory.T.symmetric_invertible_exists_posdef_congruence _ _ ?_ ?_` and prove the remaining obligations. Conclude with `hBs.map _`. Establish `h` using `RingHom.map_det (ρ w) B`. Rewrite `h` using `[RingHom.mapMatrix_apply]`.

Rewrite using `[← h]`. Conclude with `(map_ne_zero _).2 hBd`. Use `choose Pm hPd hPm using hP`. Establish `hcard : Fintype.card (Fin M × Fin d) = 2 * M` using `by simp [hd, mul_comm]`. Take `⟨Di, hDc, -, hDd, -⟩` from `GlobalTheory.T.quadratic_level_set_density F (Fin M × Fin d) M B ρ Pm ⟨hcm.1, hcard, hBs, hBd, hρ, hPd, hPm⟩ hM`.

Use `set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκdef`. Establish `hκ : 0 < κ` using `inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by`. Conclude with `NumberField.discr_ne_zero F)))` after adjusting the coercions. Take `⟨lam, hlam, hmap⟩` from `exists_haar_map (F := F) hcm.1 e he hκ`. Use `haveI : SigmaFinite lam := inferInstance`.

Take `⟨-, hK2, hK3⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) d b lam hlam`. Use `haveI := hK2 1 M`. Use `haveI := hK3 1`. Take `⟨c₁, hc₁⟩ : ∃ c : ℝ≥0, μ = (c : ℝ≥0∞) • coordW (Ainf F) b lam 1 M` from `⟨_, (Measure.isAddLeftInvariant_eq_smul μ (coordW (Ainf F) b lam 1 M)).trans (ENNReal.smul_def _ _)⟩`. Take `⟨c₂, hc₂0, hc₂⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ ν = (c : ℝ≥0∞) • coordHerm (Ainf F) σ b lam 1` from `⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (coordHerm (Ainf F) σ b lam 1)).ne', (Measure.isAddLeftInvariant_eq_smul ν (coordHerm (Ainf F) σ b lam 1)).trans (ENNReal.smul_def _ _)⟩`.

Set `eH : Ainf F ≃ₜ (InfinitePlace F → ℝ)` to `he.homeomorph e`. Set `tt` to `HermOne.hermHomeo (Ainf F) (σ := σ) hcm`. Set `τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ)` to `tt.trans eH`. Establish `hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0))` using `fun _ => rfl`. Establish `hpush : (coordHerm (Ainf F) σ b lam 1).map τ = ENNReal.ofReal κ • volume`.

Establish `h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt` using `rfl`. Rewrite using `[h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable, HermOne.map_coordHerm (Ainf F) hcm b lam, hmap]`. Establish `hcoord` using `GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b lam hlam M`. Set `Φh : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin M × Fin d → ℝ)` to `(hcoord.1.homeomorph _).trans (swapHomeo eH)`. Set `Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ)` to `fun X w => xw e b X w`.

Establish `hΦh : ∀ X, Φh X = Φ X` using `fun _ => rfl`. Establish `hΦm : Measurable Φ` using `(swapHomeo (ι := Fin M × Fin d) eH).continuous.measurable.comp hcoord.2.1.measurable`. Establish `hpushL : (coordW (Ainf F) b lam 1 M).map Φ = ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ))` using `GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he lam hlam hmap`. Set `A₀ : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ` to `fun w => B.map (ρ w)`. Establish `hQc : Continuous (qR0 A₀)`.

Use `continuous_pi fun w => continuous_const.mul ?_` and prove the remaining obligations. Conclude with `(continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))`. Set `f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ` to `fun x => φ (Φh.symm x)`. Establish `hfc : Continuous f` using `hφc.comp Φh.symm.continuous`. Establish `hfΦ : ∀ X, f (Φ X) = φ X` using `fun X => by show φ (Φh.symm (Φ X)) = φ X`.

Rewrite using `[← hΦh, Homeomorph.symm_apply_apply]`. Establish `hfR : ∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C'`. Introduce `N`. Take `⟨C, hC⟩` from `hφR N`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hC (Φh.symm x)`. Rewrite `h1` using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]`. Use `le_trans ?_ h1` and prove the remaining obligations. Establish `h2 : ∑ w, ‖x w‖ ≤ sizeTup b (Φh.symm x)`. Establish `h3` using `sum_norm_xw_le b e hen (Φh.symm x)`.

Establish `h4 : (fun w => xw e b (Φh.symm x) w) = x` using `Φh.apply_symm_apply x`. Simplify `h3` using `only [h4]`. Establish `h0 : 0 ≤ ∑ w, ‖x w‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (hφ0 _)`. Take `⟨ε', hε', hconst⟩` from `exists_small_const c₁ c₂ hc₂0 hκ (pow_nonneg hκ.le (M * d)) hε`.

Take `⟨δ, R, hδ, hR, hbound⟩` from `hreal A₀ Pm Di hDc hDd f hfc.measurable (fun _ => hφ0 _) hfR ε' hε'`. Use `⟨δ, R, hδ, hR, Φh.isCompact_preimage.2 (isCompact_coreR δ hR), fun A hA => ?_⟩` and prove the remaining obligations. Use `set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' A with hU'def`. Establish `hU' : MeasurableSet U'` using `τ.symm.measurable hA`. Establish `hpre : τ ⁻¹' U' = A`.

Use extensionality with `S`. Simplify using `[hU'def]`. Establish `hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) = Φ ⁻¹' (qR0 A₀ ⁻¹' U')`. Use extensionality with `X`. Establish `hmem` using `InfDens.gramR_mem (Ainf F) hs hJ.1 X`.

Establish `hQ : qR0 A₀ (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩`. Use function extensionality and compare the values at `w`. Rewrite using `[hτ]`. Conclude with `(InfDens.e_half_trace b B (hBR (Ainf F)).1 ρ e heρ X w).symm`. Simplify using `only [Set.mem_preimage, hU'def]`.

Rewrite using `[hQ, Homeomorph.symm_apply_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hSX⟩`. Establish `: (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S` using `Subtype.ext hSX.symm`. Rewrite using `[this]` and apply the resulting hypothesis.

Introduce `h`. Conclude with `⟨_, h, rfl⟩`. Establish `hS : MeasurableSet (qR0 A₀ ⁻¹' U' ∩ (coreR δ R)ᶜ)` using `(hQc.measurable hU').inter (isClosed_coreR δ R).measurableSet.compl`. Establish `hL : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) ∩ {X | (fun w => xw e b X w) ∈ coreR δ R}ᶜ, ENNReal.ofReal (φ X) ∂μ = (c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) * ∫⁻ x in qR0 A₀ ⁻¹' U' ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x))`. Establish `h2` using `setLIntegral_map (μ := coordW (Ainf F) b lam 1 M) hS hfc.measurable.ennreal_ofReal hΦm`.

Rewrite `h2` using `[hpushL, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]`. Rewrite using `[h2, hc₁, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, hset]`. Simplify using `only [hfΦ]`. Both sides reduce to the same expression. Establish `hνA : ν A = (c₂ : ℝ≥0∞) * (ENNReal.ofReal κ * volume U')`.

Establish `h1 : coordHerm (Ainf F) σ b lam 1 A = ((coordHerm (Ainf F) σ b lam 1).map τ) U'`. Rewrite using `[Measure.map_apply τ.measurable hU', hpre]`. Rewrite using `[hc₂, Measure.smul_apply, smul_eq_mul, h1, hpush, Measure.smul_apply, smul_eq_mul]`. Rewrite using `[hL, hνA]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hbound U' hU'`. Use `_ = ((c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) * ENNReal.ofReal ε')) * volume U' := by ring`. Use `_ ≤ (ENNReal.ofReal ε * ((c₂ : ℝ≥0∞) * ENNReal.ofReal κ)) * volume U' := by gcongr`. Use `_ = ENNReal.ofReal ε * ((c₂ : ℝ≥0∞) * (ENNReal.ofReal κ * volume U')) := by ring`.
-/
theorem smallDensity_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → (∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U) → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ IsCompact {X : Fin 1 → Fin M → Ainf F ⊗[F] E | (fun w => xw e b X w) ∈ coreR δ R} ∧ ∀ A : Set (HermR (Ainf F) σ 1), MeasurableSet A → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) ∩ {X | (fun w => xw e b X w) ∈ coreR δ R}ᶜ, ENNReal.ofReal (φ X) ∂μ ≤ ENNReal.ofReal ε * ν A := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM d b ρ e hρ he heρ hen hreal μ ν hμ hν φ hφc hφ0 hφR ε hε
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (HermR (Ainf F) σ 1) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, t9, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 M
  haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → Ainf F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ainf F ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (Ainf F) σ 1) :=
    (t9 1).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (Ainf F) σ 1) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hcm.2.2.1] at h1
    simpa using h1.symm
  have hs : ∀ x, σ (σ x) = x := HermOne.sig_sig hcm
  obtain ⟨B, hBs, hBd, -, hBR⟩ := GlobalTheory.T.exists_trace_form_gram_matrix_in_basis F E σ hcm M J hJ d b
  have hP : ∀ w, ∃ P : Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ,
      P.PosDef ∧ P * (B.map (ρ w))⁻¹ * P = B.map (ρ w) := by
    intro w
    refine GlobalTheory.T.symmetric_invertible_exists_posdef_congruence _ _ ?_ ?_
    · exact hBs.map _
    · have h := RingHom.map_det (ρ w) B
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero _).2 hBd
  choose Pm hPd hPm using hP
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by simp [hd, mul_comm]
  obtain ⟨Di, hDc, -, hDd, -⟩ := GlobalTheory.T.quadratic_level_set_density F (Fin M × Fin d) M B ρ Pm
    ⟨hcm.1, hcard, hBs, hBd, hρ, hPd, hPm⟩ hM

  set κ : ℝ := (Real.sqrt |(discr F : ℝ)|)⁻¹ with hκdef
  have hκ : 0 < κ := inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by
    exact_mod_cast NumberField.discr_ne_zero F)))
  obtain ⟨lam, hlam, hmap⟩ := exists_haar_map (F := F) hcm.1 e he hκ
  haveI : SigmaFinite lam := inferInstance
  obtain ⟨-, hK2, hK3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) d b lam hlam
  haveI := hK2 1 M
  haveI := hK3 1
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ≥0, μ = (c : ℝ≥0∞) • coordW (Ainf F) b lam 1 M :=
    ⟨_, (Measure.isAddLeftInvariant_eq_smul μ (coordW (Ainf F) b lam 1 M)).trans
      (ENNReal.smul_def _ _)⟩
  obtain ⟨c₂, hc₂0, hc₂⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ ν = (c : ℝ≥0∞) • coordHerm (Ainf F) σ b lam 1 :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (coordHerm (Ainf F) σ b lam 1)).ne',
      (Measure.isAddLeftInvariant_eq_smul ν (coordHerm (Ainf F) σ b lam 1)).trans
      (ENNReal.smul_def _ _)⟩

  let eH : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  let tt := HermOne.hermHomeo (Ainf F) (σ := σ) hcm
  let τ : HermR (Ainf F) σ 1 ≃ₜ (InfinitePlace F → ℝ) := tt.trans eH
  have hτ : ∀ S, τ S = e (algebraMap F (Ainf F) (1 / 2) *
      Algebra.trace (Ainf F) (Ainf F ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) 0 0)) :=
    fun _ => rfl
  have hpush : (coordHerm (Ainf F) σ b lam 1).map τ = ENNReal.ofReal κ • volume := by
    have h1 : (τ : HermR (Ainf F) σ 1 → _) = e ∘ tt := rfl
    rw [h1, ← Measure.map_map (f := tt) (g := e) eH.measurable tt.measurable,
      HermOne.map_coordHerm (Ainf F) hcm b lam, hmap]
  have hcoord := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hcm (Ainf F) d b lam hlam M
  let Φh : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin M × Fin d → ℝ) :=
    (hcoord.1.homeomorph _).trans (swapHomeo eH)
  let Φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → (InfinitePlace F → Fin M × Fin d → ℝ) :=
    fun X w => xw e b X w
  have hΦh : ∀ X, Φh X = Φ X := fun _ => rfl
  have hΦm : Measurable Φ :=
    (swapHomeo (ι := Fin M × Fin d) eH).continuous.measurable.comp hcoord.2.1.measurable
  have hpushL : (coordW (Ainf F) b lam 1 M).map Φ =
      ENNReal.ofReal (κ ^ (M * d)) • (volume : Measure (InfinitePlace F → Fin M × Fin d → ℝ)) :=
    GlobalTheory.T.archimedean_coordinate_measure_transport F E σ hcm M d b e he lam hlam hmap
  let A₀ : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ := fun w => B.map (ρ w)
  have hQc : Continuous (qR0 A₀) := by
    refine continuous_pi fun w => continuous_const.mul ?_
    exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))

  let f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ := fun x => φ (Φh.symm x)
  have hfc : Continuous f := hφc.comp Φh.symm.continuous
  have hfΦ : ∀ X, f (Φ X) = φ X := fun X => by
    show φ (Φh.symm (Φ X)) = φ X
    rw [← hΦh, Homeomorph.symm_apply_apply]
  have hfR : ∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C' := by
    intro N
    obtain ⟨C, hC⟩ := hφR N
    refine ⟨C, fun x => ?_⟩
    have h1 := hC (Φh.symm x)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ0 _)] at h1
    refine le_trans ?_ h1
    have h2 : ∑ w, ‖x w‖ ≤ sizeTup b (Φh.symm x) := by
      have h3 := sum_norm_xw_le b e hen (Φh.symm x)
      have h4 : (fun w => xw e b (Φh.symm x) w) = x := Φh.apply_symm_apply x
      simpa only [h4] using h3
    have h0 : 0 ≤ ∑ w, ‖x w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (hφ0 _)
  obtain ⟨ε', hε', hconst⟩ := exists_small_const c₁ c₂ hc₂0 hκ
    (pow_nonneg hκ.le (M * d)) hε
  obtain ⟨δ, R, hδ, hR, hbound⟩ := hreal A₀ Pm Di hDc hDd f hfc.measurable (fun _ => hφ0 _) hfR
    ε' hε'
  refine ⟨δ, R, hδ, hR, Φh.isCompact_preimage.2 (isCompact_coreR δ hR), fun A hA => ?_⟩
  set U' : Set (InfinitePlace F → ℝ) := τ.symm ⁻¹' A with hU'def
  have hU' : MeasurableSet U' := τ.symm.measurable hA
  have hpre : τ ⁻¹' U' = A := by
    ext S
    simp [hU'def]
  have hset : gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) = Φ ⁻¹' (qR0 A₀ ⁻¹' U') := by
    ext X
    have hmem := InfDens.gramR_mem (Ainf F) hs hJ.1 X
    have hQ : qR0 A₀ (Φ X) = τ ⟨gramR (Ainf F) σ J X, hmem⟩ := by
      funext w
      rw [hτ]
      exact (InfDens.e_half_trace b B (hBR (Ainf F)).1 ρ e heρ X w).symm
    simp only [Set.mem_preimage, hU'def]
    rw [hQ, Homeomorph.symm_apply_apply]
    constructor
    · rintro ⟨S, hS, hSX⟩
      have : (⟨gramR (Ainf F) σ J X, hmem⟩ : HermR (Ainf F) σ 1) = S := Subtype.ext hSX.symm
      rwa [this]
    · intro h
      exact ⟨_, h, rfl⟩
  have hS : MeasurableSet (qR0 A₀ ⁻¹' U' ∩ (coreR δ R)ᶜ) :=
    (hQc.measurable hU').inter (isClosed_coreR δ R).measurableSet.compl
  have hL : ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' A) ∩ {X | (fun w => xw e b X w) ∈ coreR δ R}ᶜ,
        ENNReal.ofReal (φ X) ∂μ =
      (c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) *
        ∫⁻ x in qR0 A₀ ⁻¹' U' ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x)) := by
    have h2 := setLIntegral_map (μ := coordW (Ainf F) b lam 1 M) hS
      hfc.measurable.ennreal_ofReal hΦm
    rw [hpushL, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul] at h2
    rw [h2, hc₁, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, hset]
    simp only [hfΦ]
    rfl
  have hνA : ν A = (c₂ : ℝ≥0∞) * (ENNReal.ofReal κ * volume U') := by
    have h1 : coordHerm (Ainf F) σ b lam 1 A = ((coordHerm (Ainf F) σ b lam 1).map τ) U' := by
      rw [Measure.map_apply τ.measurable hU', hpre]
    rw [hc₂, Measure.smul_apply, smul_eq_mul, h1, hpush, Measure.smul_apply, smul_eq_mul]
  rw [hL, hνA]
  calc (c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) *
        ∫⁻ x in qR0 A₀ ⁻¹' U' ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x))
      ≤ (c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) * (ENNReal.ofReal ε' * volume U')) := by
        gcongr
        exact hbound U' hU'
    _ = ((c₁ : ℝ≥0∞) * (ENNReal.ofReal (κ ^ (M * d)) * ENNReal.ofReal ε')) * volume U' := by ring
    _ ≤ (ENNReal.ofReal ε * ((c₂ : ℝ≥0∞) * ENNReal.ofReal κ)) * volume U' := by gcongr
    _ = ENNReal.ofReal ε * ((c₂ : ℝ≥0∞) * (ENNReal.ofReal κ * volume U')) := by ring

end GlobalTheory.CompanionTheory.SW.BB.InfTransport
