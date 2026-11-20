import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianPointEmbeddingInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGradientEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.ConvexSeparationPositiveDistance
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceLogEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormCauchySchwarzCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

/- English proof (translation)
Simplify using `[trF, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]`.
-/
private theorem trF_sub_smul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (X W : Matrix (Fin a) (Fin a) (Cinf E)) (r : ℝ) :
    trF (X - r • (1 : Matrix (Fin a) (Fin a) (Cinf E))) W = trF X W - r * trF 1 W := by
  simp [trF, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

/- English proof (translation)
Rewrite using `[← norm_euc_sq]`. Conclude with `pow_pos (norm_pos_iff.2 fun h => hw (euc.map_eq_zero_iff.1 h)) 2`.
-/
private theorem qf_pos {E : Type} [Field E] [NumberField E] {a : ℕ} {w : Fin a → Cinf E} (hw : w ≠ 0) :
    0 < qf w := by
  rw [← norm_euc_sq]
  exact pow_pos (norm_pos_iff.2 fun h => hw (euc.map_eq_zero_iff.1 h)) 2

/- English proof (translation)
Introduce `E _ _ _ a ha L hL`. Take `⟨cA, hcA, hA⟩` from `UpperTheory.hermitian_point_embedding_injective E a ha L hL`. Take `⟨CB, hB⟩` from `UpperTheory.hermitian_space_gradient_estimate E a ha L hL`. Take `⟨c, C, N, hc, hS⟩` from `UpperTheory.convex_separation_positive_distance E a ha L hL`. Take `⟨CF, hF⟩` from `UpperTheory.hermitian_space_log_estimate E a ha L hL`.

Establish `hT` using `(UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1`. Establish `hq` using `(UpperTheory.V.Lit.Geo.qhtFacts E a).1`. Use `set δ : ℝ := cA / 2 * c ^ 2 / (|CB| + 1) with hδ`. Establish `hδ0 : 0 < δ` using `by positivity`. Use `⟨(cA / 2) ^ 2, max (Real.log 2) (|CF| * (1 + Real.log (C / δ ^ N)) + 1), by positivity, fun g hg => ?_⟩` and prove the remaining obligations.

Establish `h2 : 2 ≤ Th L g` using `(Real.log_le_log_iff two_pos (one_pos.trans_le (hT g).1)).1 ((le_max_left _ _).trans hg)`. Take `⟨w, hw, hwC, hwv⟩` from `hS g`. Establish `hw0` using `qf_pos hw`. Establish `hq1 : 1 ≤ qht g` using `hq g`. Establish `hsm : qf w ≤ δ`.

Assume the negation of the conclusion as `hn`. Establish `h1 : qht g ≤ C / δ ^ N`. Rewrite using `[le_div_iff₀ (by positivity)]`. Conclude with `(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le (not_le.1 hn).le N) (by linarith)).trans hwC`. Establish `h3` using `Real.log_le_log (by linarith) h1`.

Establish `h4` using `Real.log_nonneg hq1`. Establish `h5` using `(le_max_right _ _).trans hg`. Establish `h6 : CF * (1 + Real.log (qht g)) ≤ |CF| * (1 + Real.log (C / δ ^ N))` using `mul_le_mul (le_abs_self _) (by linarith) (by linarith) (abs_nonneg _)`. Combine the linear relations using `[hF g]`. Take `⟨r1, r2, -⟩` from `UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w`.

Establish `hb` using `hB g w c hc hwv`. Establish `ha'` using `hA g h2`. Establish `hb' : CB * qf w ^ 2 / c ^ 2 ≤ cA / 2 * qf w`. Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `h7 : qf w * (|CB| + 1) ≤ cA / 2 * c ^ 2` using `(le_div_iff₀ (by positivity)).1 hsm`.

Establish `h8 : CB ≤ |CB| + 1` using `(le_abs_self _).trans (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `he : trF (dev L g).1 (vecMulVec w (star w)) = trF (mom L g).1 (vecMulVec w (star w)) - ell E a (toL (mom L g).1) * qf w`. Rewrite using `[← r1, ← trF_sub_smul]`. Both sides reduce to the same expression.

Establish `h9 : cA / 2 * qf w ≤ -trF (dev L g).1 (vecMulVec w (star w))`. Rewrite using `[he]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right ha' hw0.le]`. Establish `h10` using `pow_le_pow_left₀ (by positivity) h9 2`. Rewrite `h10` using `[neg_sq, mul_pow]`.

Conclude with `le_of_mul_le_mul_right (h10.trans (r2 (dev L g))) (by positivity)`.
-/
theorem UpperTheory.traceForm_posDef_of_totallyReal :
    Grad := by
  intro E _ _ _ a ha L hL
  obtain ⟨cA, hcA, hA⟩ := UpperTheory.hermitian_point_embedding_injective E a ha L hL
  obtain ⟨CB, hB⟩ := UpperTheory.hermitian_space_gradient_estimate E a ha L hL
  obtain ⟨c, C, N, hc, hS⟩ := UpperTheory.convex_separation_positive_distance E a ha L hL
  obtain ⟨CF, hF⟩ := UpperTheory.hermitian_space_log_estimate E a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  have hq := (UpperTheory.V.Lit.Geo.qhtFacts E a).1
  set δ : ℝ := cA / 2 * c ^ 2 / (|CB| + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(cA / 2) ^ 2, max (Real.log 2) (|CF| * (1 + Real.log (C / δ ^ N)) + 1), by positivity, fun g hg => ?_⟩
  have h2 : 2 ≤ Th L g :=
    (Real.log_le_log_iff two_pos (one_pos.trans_le (hT g).1)).1 ((le_max_left _ _).trans hg)
  obtain ⟨w, hw, hwC, hwv⟩ := hS g
  have hw0 := qf_pos hw
  have hq1 : 1 ≤ qht g := hq g
  have hsm : qf w ≤ δ := by
    by_contra hn
    have h1 : qht g ≤ C / δ ^ N := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le (not_le.1 hn).le N) (by linarith)).trans hwC
    have h3 := Real.log_le_log (by linarith) h1
    have h4 := Real.log_nonneg hq1
    have h5 := (le_max_right _ _).trans hg
    have h6 : CF * (1 + Real.log (qht g)) ≤ |CF| * (1 + Real.log (C / δ ^ N)) :=
      mul_le_mul (le_abs_self _) (by linarith) (by linarith) (abs_nonneg _)
    linarith [hF g]
  obtain ⟨r1, r2, -⟩ := UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w
  have hb := hB g w c hc hwv
  have ha' := hA g h2
  have hb' : CB * qf w ^ 2 / c ^ 2 ≤ cA / 2 * qf w := by
    rw [div_le_iff₀ (by positivity)]
    have h7 : qf w * (|CB| + 1) ≤ cA / 2 * c ^ 2 := (le_div_iff₀ (by positivity)).1 hsm
    have h8 : CB ≤ |CB| + 1 := (le_abs_self _).trans (by linarith)
    calc CB * qf w ^ 2 ≤ (|CB| + 1) * qf w ^ 2 := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = qf w * (|CB| + 1) * qf w := by ring
      _ ≤ cA / 2 * c ^ 2 * qf w := mul_le_mul_of_nonneg_right h7 hw0.le
      _ = _ := by ring
  have he : trF (dev L g).1 (vecMulVec w (star w)) =
      trF (mom L g).1 (vecMulVec w (star w)) - ell E a (toL (mom L g).1) * qf w := by
    rw [← r1, ← trF_sub_smul]
    rfl
  have h9 : cA / 2 * qf w ≤ -trF (dev L g).1 (vecMulVec w (star w)) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right ha' hw0.le]
  have h10 := pow_le_pow_left₀ (by positivity) h9 2
  rw [neg_sq, mul_pow] at h10
  exact le_of_mul_le_mul_right (h10.trans (r2 (dev L g))) (by positivity)
