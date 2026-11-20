import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAddStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamPet

open scoped ENNReal

/- English proof (translation)
Establish `hApos : 0 < A.toReal` using `ENNReal.toReal_pos hA0 hA`. Establish `hK0 : 0 ≤ K`. Assume the negation of the conclusion as `hK`. Rewrite `h` using `[ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul]`. Conclude with `hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))`.

Establish `h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2`. Use `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow]`. Then use the resulting hypothesis. Establish `hB0 : 0 < B.toReal`. Break down `(ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb` into its components or cases.

Conclude with `hb`. Rewrite `h2` using `[← hb]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hKpos : 0 < K`. Assume the negation of the conclusion as `hK`.

Establish `: K * B.toReal ^ 2 ≤ 0` using `mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨mul_pos hL hB0, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']`. Establish `h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2)` using `Real.log_le_log (by positivity) h2`.

Rewrite `h3` using `[Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow]`. Move the coercions through the operations in `at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_le_of_sq_le {A B : ℝ≥0∞} {K L : ℝ} (hL : 0 < L) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hA0 : A ≠ 0)
    (h : A ^ 2 ≤ ENNReal.ofReal K * B ^ 2) :
    0 < L * B.toReal ∧ Real.log (L * A.toReal) ≤ 1 / 2 * Real.log K + Real.log (L * B.toReal) := by
  have hApos : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hK0 : 0 ≤ K := by
    by_contra hK
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul] at h
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))
  have h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow] at this
  have hB0 : 0 < B.toReal := by
    rcases (ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb
    · exact hb
    · rw [← hb] at h2; nlinarith
  have hKpos : 0 < K := by
    by_contra hK
    have : K * B.toReal ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)
    nlinarith
  refine ⟨mul_pos hL hB0, ?_⟩
  rw [Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']
  have h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow] at h3
  push_cast at h3
  linarith

/- English proof (translation)
Introduce `hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0`. Establish `hFc : (F : Rul Xo c) ∈ cusp Xo c U a n` using `cuspW_wtZ (Xo := Xo) (c := c) (U := U) a n ▸ F.2`. Establish `hF0' : (F : Rul Xo c) ≠ 0` using `fun h => hF0 (Subtype.ext h)`. Establish `hsup` using `GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel D j H Dw l Xo c U dict hL χ hχ a n hD _ hFc hF hF0'`. Establish `hsl` using `GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL`.

Establish `hsp` using `GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL`. Establish `hdef : Formalism.L2.Pj.SupDef Xo c U` using `(Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp _ H Dw l Xo c _ _ hL.unf)`. Use `set x := xiR D`. Use `set K := supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) with hK`. Establish `hper : ∀ σ : c.F →+* ℂ, 0 < normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F ∧ Real.log (supC Xo c U x (goodOf c σ) a n F) ≤ 1 / 2 * Real.log K + Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F)`.

Introduce `σ`. Establish `hσ : GoodEmb c (goodOf c σ)` using `Formalism.L2.PjFree.goodEmb_goodOf c σ`. Establish `hhol` using `((mem_cusp Xo c U a n _).1 hFc).2 _ hσ`. Establish `hw : (0 : ℝ) < ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1` using `by positivity`. Establish `hb` using `hsl _ hσ (laU (U (goodOf c σ)) a n) _ hw (fun k => (hsp _ hσ a n k).trans (by linarith)) (hL.chiTriv _ hσ a n hD) _ hhol`.

Establish `hne0 : supE (U (goodOf c σ)).X (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ 0`. Introduce `h0`. Use `hF0' (hdef a n hD _ hσ _ hFc ?_)` and prove the remaining obligations. Unfold `supN`. Rewrite using `[h0, ENNReal.toReal_zero]`.

Establish `hfin` using `supE_cusp_ne_top hσ hFc`. Take `⟨_, _, _, _, _, hdu, _⟩` from `hL.dictU _ hσ`. Establish `hpfin : petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ ⊤` using `petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hhol`. Establish `key` using `log_le_of_sq_le (lieFac_pos Dw x a) hfin hpfin hne0 hb`. Establish `e : normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F = lieFac Dw x a * (petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F)).toReal` using `by show lieFacZ Dw x (wtZ a n) * _ = _`.

Rewrite using `[lieFacZ_wtZ, modelWt_wtZ]`. Rewrite using `[e]`. Conclude with `key`. Use `⟨fun σ => (hper σ).1, ?_⟩` and prove the remaining obligations. Establish `hN : (0 : ℝ) < (Module.finrank ℚ c.F : ℝ)` using `by exact_mod_cast Module.finrank_pos`.

Establish `hcard : (Finset.univ : Finset (c.F →+* ℂ)).card = Module.finrank ℚ c.F`. Rewrite using `[Finset.card_univ]`. Conclude with `NumberField.Embeddings.card c.F ℂ`. Establish `hsum : (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U x (goodOf c σ) a n F)) - (Module.finrank ℚ c.F : ℝ) * (1 / 2 * Real.log K) ≤ ∑ σ : c.F →+* ℂ, Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F)`. Use `Finset.sum_le_sum (s := Finset.univ) fun σ _ => (hper σ).2` as an intermediate fact.

Rewrite `this` using `[Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) = lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ …` using `rfl`. Rewrite using `[e, le_div_iff₀ hN]`. Rewrite `hsup` using `[le_div_iff₀ hN]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem mean_log_petersson_ge : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro hM hT D j H Dw l Xo c U dict hL _ χ hχ a n hD F hF hF0
  have hFc : (F : Rul Xo c) ∈ cusp Xo c U a n := cuspW_wtZ (Xo := Xo) (c := c) (U := U) a n ▸ F.2
  have hF0' : (F : Rul Xo c) ≠ 0 := fun h => hF0 (Subtype.ext h)
  have hsup := GlobalTheory.T.meanLogSupNorm_lowerBound_principalLevel D j H Dw l Xo c U dict hL χ hχ a n hD _ hFc hF hF0'
  have hsl := GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL
  have hdef : Formalism.L2.Pj.SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp _ H Dw l Xo c _ _ hL.unf)
  set x := xiR D
  set K := supConst D.host.E D.R.r D.host.d l.M
    (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) with hK
  have hper : ∀ σ : c.F →+* ℂ, 0 < normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F ∧
      Real.log (supC Xo c U x (goodOf c σ) a n F) ≤
        1 / 2 * Real.log K + Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    intro σ
    have hσ : GoodEmb c (goodOf c σ) := Formalism.L2.PjFree.goodEmb_goodOf c σ
    have hhol := ((mem_cusp Xo c U a n _).1 hFc).2 _ hσ
    have hw : (0 : ℝ) < ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := by positivity
    have hb := hsl _ hσ (laU (U (goodOf c σ)) a n) _ hw
      (fun k => (hsp _ hσ a n k).trans (by linarith)) (hL.chiTriv _ hσ a n hD) _ hhol
    have hne0 : supE (U (goodOf c σ)).X (laU (U (goodOf c σ)) a n) (rdU (U (goodOf c σ)) F) ≠ 0 := by
      intro h0
      refine hF0' (hdef a n hD _ hσ _ hFc ?_)
      unfold supN; rw [h0, ENNReal.toReal_zero]
    have hfin := supE_cusp_ne_top hσ hFc
    obtain ⟨_, _, _, _, _, hdu, _⟩ := hL.dictU _ hσ
    have hpfin : petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
        (rdU (U (goodOf c σ)) F) ≠ ⊤ :=
      petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hhol
    have key := log_le_of_sq_le (lieFac_pos Dw x a) hfin hpfin hne0 hb
    have e : normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F = lieFac Dw x a *
        (petE (D.sp.W j) (dict (goodOf c σ)) (muQ1 (D.sp.W j)) (laU (U (goodOf c σ)) a n)
          (rdU (U (goodOf c σ)) F)).toReal := by
      show lieFacZ Dw x (wtZ a n) * _ = _
      rw [lieFacZ_wtZ, modelWt_wtZ]
    rw [e]
    exact key
  refine ⟨fun σ => (hper σ).1, ?_⟩
  have hN : (0 : ℝ) < (Module.finrank ℚ c.F : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (c.F →+* ℂ)).card = Module.finrank ℚ c.F := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card c.F ℂ
  have hsum : (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U x (goodOf c σ) a n F)) -
      (Module.finrank ℚ c.F : ℝ) * (1 / 2 * Real.log K) ≤
      ∑ σ : c.F →+* ℂ, Real.log (normW U x (fun _ => D.sp.W j) dict (wtZ a n) σ F) := by
    have := Finset.sum_le_sum (s := Finset.univ) fun σ _ => (hper σ).2
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
    linarith
  have e : lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ)
      ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) = lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re
      ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 / 2 * Real.log K := rfl
  rw [e, le_div_iff₀ hN]
  rw [le_div_iff₀ hN] at hsup
  nlinarith

end GlobalTheory.LamPet
