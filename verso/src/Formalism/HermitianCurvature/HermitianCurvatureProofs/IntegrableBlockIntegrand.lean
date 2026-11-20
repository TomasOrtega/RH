import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/- English proof (translation)
Use `Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)` and prove the remaining obligations. Conclude with `max_le (by linarith) (by linarith)`.
-/
theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

/- English proof (translation)
Unfold `lowRow`. Conclude with `P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const`.
-/
theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

/- English proof (translation)
The claim follows from `P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const`.
-/
theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

/- English proof (translation)
Unfold `orbM`. Use `Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_` and prove the remaining obligations. Conclude with `(continuous_blkU n).comp (continuous_snd)`.
-/
theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

/- English proof (translation)
Establish `ha0 : 0 ≤ a` using `le_trans (by positivity) ha.le`. Establish `hK : 0 ≤ K`. Establish `h` using `hb 0`. Assume the negation of the conclusion as `hn`. Establish `: K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0` using `mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)`.

Combine the linear relations using `[norm_nonneg (Φ (orbM (m + 1) t c 0))]`. Establish `hpt : ∀ p : BlockCoord (m + 1), ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a)`. Introduce `p`. Rewrite using `[P.OrbitTailEstimates.norm_blockIntegrand]`. Use `(hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)` and prove the remaining obligations.

Conclude with `maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0`. Take `⟨k, hk⟩` from `P.G7.muBlock_eq β (m + 1)`. Establish `i3 : BorelSpace (BlockCoord (m + 1))` using `inferInstance`. Establish `j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`. Establish `j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`.

Establish `hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a`. Rewrite using `[P.OrbitTailEstimates.finrank_block_cast]`. Conclude with `ha`. Establish `hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1))`. Rewrite using `[hk]`.

Conclude with `(P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal`. Establish `hJ` using `P.G7.jacobian (m + 1) β t ht`. Establish `hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a)) (muBlock β (m + 1))`. Establish `h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1)))` using `hJ ▸ hI.smul_measure_nnreal`. Conclude with `(P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2`.

Establish `hcont : Continuous (blockIntegrand β (m + 1) Φ t c)`. Unfold `blockIntegrand`. Use `Continuous.smul ?_ ?_` and prove the remaining obligations. Establish `h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1)`. Unfold `G.subSum`.

Conclude with `continuous_finsetSum _ fun i _ => (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))`. Establish `h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1)`. Unfold `G.superSum`. Conclude with `continuous_finsetSum _ fun i _ => (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))`. Conclude with `((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)`.

Conclude with `continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt`. Conclude with `(hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)`.
-/
theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

/- English proof (translation)
Establish `ha0 : 0 ≤ a` using `le_trans (Nat.cast_nonneg _) ha.le`. Establish `hK : 0 ≤ K`. Establish `h` using `hb 0`. Assume the negation of the conclusion as `hn`. Establish `: K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0` using `mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)`.

Combine the linear relations using `[norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]`. Establish `hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v)` using `by show Continuous (fun v : UT (n + 1) → ℂ => ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))`. Conclude with `continuous_const.matrix_mul P.Dx2.SL.cont_upper`. Establish `hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v))` using `continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt`. Establish `hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)))`.

Establish `h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v)`. Unfold `superSum`. Conclude with `continuous_finsetSum _ fun i _ => (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)`. Conclude with `(P.G7.continuous_psi _).comp h1`. Establish `hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a)`.

Introduce `v`. Rewrite using `[norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]`. Use `(hb v).trans ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK` as an intermediate fact. Rewrite `this` using `[← mul_assoc]`.

Conclude with `this`. Rewrite using `[P.Dx2.SL.muPi_betaU]`. Apply `Integrable.smul_measure_nnreal` to reduce the goal to its premises. Conclude with `((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono' (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)`.
-/
theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

/- English proof (translation)
Unfold `OmBlock`. Rewrite using `[← L.integral_comp_comm hI]`. Use `integral_congr_ae (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [blockIntegrand, L.map_smul]`.
-/
theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

/- English proof (translation)
Unfold `OmLong`. Rewrite using `[← L.integral_comp_comm hI]`. Use `integral_congr_ae (Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [L.map_smul]`.
-/
theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
