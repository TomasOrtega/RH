import Mathlib
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussDensSphere
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliserStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.UnitaryVolume

/- English proof (translation)
Simplify using `[Formalism.REAL.Jm, allPos]`.
-/
theorem Jm_allPos (N : ℕ) : Formalism.REAL.Jm (allPos N) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

/- English proof (translation)
Establish `h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N)` using `g.2`. Rewrite `h` using `[Jm_allPos, Matrix.mul_one]`. Conclude with `mul_eq_one_comm.1 h`.
-/
theorem mul_conjTranspose_self {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : uMat g * (uMat g)ᴴ = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  rw [Jm_allPos, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

/- English proof (translation)
Establish `h` using `congrFun (congrFun (mul_conjTranspose_self g) i) i`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h`. Establish `h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1`. Rewrite using `[← h]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `(Complex.mul_conj' _).symm`. Conclude with `h2` after adjusting the coercions.
-/
theorem row_norm {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) (i : Fin N) : ∑ k, ‖uMat g i k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_self g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast h2

/- English proof (translation)
Establish `h` using `Formalism.REAL.ballFinite N (allPos N) N`. Establish `e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ`. Use `Set.eq_univ_of_forall fun g => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)`. Simplify using `[row_norm]`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem muG_univ_lt_top (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ < ⊤ := by
  have h := Formalism.REAL.ballFinite N (allPos N) N
  have e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    change ∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)
    simp [row_norm]
  rwa [e] at h

/- English proof (translation)
The claim follows from `(isOpen_univ.measure_pos _ Set.univ_nonempty).ne'`.
-/
theorem muG_univ_ne_zero (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ ≠ 0 :=
  (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

/- English proof (translation)
Rewrite using `[Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]`. Use `congr 2`. Rewrite using `[← row_norm g 0]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.mulVec_single_one, Matrix.conjTranspose_apply]`.
-/
theorem gauss_inv_single {n : ℕ} (g : Formalism.REAL.UJ (allPos (n + 1))) :
    gauss ((uMat g)⁻¹ *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Real.exp (-1) := by
  rw [Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]
  congr 2
  rw [← row_norm g 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n`. Rewrite using `[← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]`. Simplify using `[add_comm]`. Unfold `volU sphV`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), h]`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volU_succ (n : ℕ) :
    volU (n + 1) = volU n * (2 ^ (n + 1) * Real.pi ^ (n + 1) / (n.factorial : ℝ)) := by
  have h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]
    simp [add_comm]
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (by omega), h]
  simp only [Nat.add_sub_cancel]
  ring

/- English proof (translation)
Unfold `volU sphV`. Use `Real.pi_pos` as an intermediate fact. Conclude with `mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)`.
-/
theorem volU_pos (n : ℕ) : 0 < volU n := by
  unfold volU sphV
  have := Real.pi_pos
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

/- English proof (translation)
Establish `h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1`. Express the relevant statement in the definitionally equal form `(volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1`. Establish `e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ` using `Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp`. Rewrite using `[e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]`. Simplify using `[volume_pi, Measure.pi_univ]`.

Unfold `IsGauge at hc`. Rewrite `hc` using `[h1]`. Establish `h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)`. Use `hc.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`.

Establish `e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ` using `Set.eq_univ_of_forall fun g => by`. Simplify `le_of_lt hr` using `[Formalism.REAL.hs]`. Rewrite using `[e]`. Simplify using the standard rewrite rules. Rewrite using `[tendsto_const_nhds_iff.1 h2]`.

Simplify using `[volU, sphV]`.
-/
theorem volume_zero (c : ℝ) (hc : IsGauge (allPos 0) c) :
    c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal = volU 0 := by
  have h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1
    have e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ :=
      Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp
    rw [e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]
    simp [volume_pi, Measure.pi_univ]
  unfold IsGauge at hc
  rw [h1] at hc
  have h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        simpa [Formalism.REAL.hs] using le_of_lt hr
    rw [e]
    simp
  rw [tendsto_const_nhds_iff.1 h2]
  simp [volU, sphV]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => exact volume_zero`. Consider the case `succ n ih`. Introduce `c hc`.

Take `⟨c₀, hc₀, -, hu⟩` from `GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))`. Establish `hcpos : 0 < c` using `by rw [hu c hc]; exact hc₀`. Take `⟨c', hc'pos, hc', -⟩` from `GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)`. Establish `hv` using `ih c' hc'`. Set `x₀ : Fin (n + 1) → ℂ` to `Pi.single 0 1`.

Set `B : Matrix (Fin (n + 1)) (Fin n) ℂ` to `(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ`. Establish `hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true`. Simplify using `[qEps, sgn, allPos, x₀, Fin.sum_univ_succ]`. Establish `hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0`. Rewrite using `[Jm_allPos, Matrix.one_mul]`.

Use function extensionality and compare the values at `k`. Simplify using `[Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]`. Establish `hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n)`. Rewrite using `[Jm_allPos, Jm_allPos, Matrix.mul_one]`. Use extensionality with `a b`.

Simplify using `[Matrix.mul_apply, B, Matrix.one_apply, eq_comm]`. Take `⟨j, -, hj⟩` from `GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl hq hx hB`. Establish `hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n)`. Rewrite using `[← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]`. Establish `key` using `GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser n _ _ true x₀ B j hq hx hB hj c c' hc hc' (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by`.

Rewrite using `[lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le, inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])`. Establish `hs : sgn ℝ true = 1` using `by simp [sgn]`. Simplify using `only [x₀, gauss_inv_single, lintegral_const] at key`. Rewrite `key` using `[hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere]`. Establish `k2` using `congrArg ENNReal.toReal key`.

Establish `hp` using `volU_pos n`. Establish `hπ` using `Real.pi_pos`. Rewrite `k2` using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le, ENNReal.toReal_ofReal (by positivity)]`. Rewrite using `[volU_succ]`. Establish `he` using `Real.exp_pos (-1)`.

Establish `hf : (0 : ℝ) < n.factorial` using `by positivity`. Clear denominators, using `at k2 ⊢` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem volume_unitary : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c →
    c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  intro N
  induction N with
  | zero => exact volume_zero
  | succ n ih =>
    intro c hc
    obtain ⟨c₀, hc₀, -, hu⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))
    have hcpos : 0 < c := by rw [hu c hc]; exact hc₀
    obtain ⟨c', hc'pos, hc', -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)
    have hv := ih c' hc'
    let x₀ : Fin (n + 1) → ℂ := Pi.single 0 1
    let B : Matrix (Fin (n + 1)) (Fin n) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ
    have hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true := by
      simp [qEps, sgn, allPos, x₀, Fin.sum_univ_succ]
    have hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0 := by
      rw [Jm_allPos, Matrix.one_mul]
      funext k
      simp [Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]
    have hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n) := by
      rw [Jm_allPos, Jm_allPos, Matrix.mul_one]
      ext a b
      simp [Matrix.mul_apply, B, Matrix.one_apply, eq_comm]
    obtain ⟨j, -, hj⟩ := GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl
      hq hx hB
    have hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n) := by
      rw [← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]
    have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser n _ _ true x₀ B j hq hx hB hj c c' hc hc'
      (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by
        rw [lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le,
          inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])
    have hs : sgn ℝ true = 1 := by simp [sgn]
    simp only [x₀, gauss_inv_single, lintegral_const] at key
    rw [hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere] at key
    have k2 := congrArg ENNReal.toReal key
    have hp := volU_pos n
    have hπ := Real.pi_pos
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le,
      ENNReal.toReal_ofReal (by positivity)] at k2
    rw [volU_succ]
    have he := Real.exp_pos (-1)
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp at k2 ⊢
    linarith

end GlobalTheory.UnitaryVolume
