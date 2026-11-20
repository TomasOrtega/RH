import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

/- English proof (translation)
Unfold `TBB.nPt`. Rewrite using `[Formalism.FourierDecayAlt.P.PBD.weight_product_append, ha.2, Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r (D.ptGG TT (a ++ [(1, c)])) (D.ptGG TT a) (fun _ _ => 1) a 1 le_rfl (by rw [ha.2]; omega)]`. Use `congr 1`. Simplify using `only [C.nAux, KB.levW]`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.

Establish `e : 1 + j + 1 - 1 = j + 1` using `by omega`. Rewrite using `[e]`. Simplify using `only [one_mul, mul_one, Nat.cast_one]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nPt_append_one (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j + 1 ≤ P.r) (c : ℂ) :
    TBB.nPt P.k P.r TT (a ++ [(1, c)]) = TBB.nPt P.k P.r TT a * KB.levW P (j + 1) c := by
  unfold TBB.nPt
  rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, ha.2,
    Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r (D.ptGG TT (a ++ [(1, c)])) (D.ptGG TT a) (fun _ _ => 1) a 1 le_rfl
      (by rw [ha.2]; omega)]
  congr 1
  simp only [C.nAux, KB.levW]
  rw [if_neg (by omega), if_neg (by omega)]
  have e : 1 + j + 1 - 1 = j + 1 := by omega
  rw [e]
  simp only [one_mul, mul_one, Nat.cast_one]
  congr 1
  ring

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r _ (fun _ _ => 1) (fun _ _ => one_pos) a 1 le_rfl (by rw [ha.2]; omega)`.
-/
theorem nPt_nonneg_loc (P : M.Par) (TT : ℝ) (a : C.LPt) (j : ℕ) (ha : D.IsLocPt a j) (hj : j ≤ P.r) :
    0 ≤ TBB.nPt P.k P.r TT a :=
  Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r _ (fun _ _ => 1) (fun _ _ => one_pos) a 1 le_rfl (by rw [ha.2]; omega)

/- English proof (translation)
Simplify using `only [KB.levW]`. Rewrite using `[if_neg (by omega)]`. Conclude with `zpow_nonneg (norm_nonneg _) _`.
-/
theorem levW_nonneg_low (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) (c : ℂ) : 0 ≤ KB.levW P (j + 1) c := by
  simp only [KB.levW]
  rw [if_neg (by omega)]
  exact zpow_nonneg (norm_nonneg _) _

/- English proof (translation)
Introduce `hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb`. Establish `hPS : KB.PStd` using `Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top`. Establish `hjr : j ≤ P.r` using `by omega`. Take `⟨φ, -, hφi, hφ, hφs⟩` from `hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1`. Use `set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w with hK`.

Establish `hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume] fun c => (K : ℂ) * φ c` using `by filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc`. Rewrite using `[hφ c hc]`. Unfold `TBB.NP`. Rewrite using `[nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c, Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]`. Establish `hl` using `Real.mul_self_sqrt (levW_nonneg_low P j hj c)`.

Rewrite using `[hK]`. Establish `: Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) * (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w …`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, integral_const_mul]`. Establish `h0` using `hφs 0`. Simplify using `only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul, Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0`.

Rewrite using `[h0]`. Unfold `TBB.NP`. Use `congr 1`. Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos ⟨ha, hb⟩, dif_pos hjr]`.

Both sides reduce to the same expression.
-/
theorem glFibre : GLFibre := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn j hj w hw hN a b ha hb
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hjr : j ≤ P.r := by omega
  obtain ⟨φ, -, hφi, hφ, hφs⟩ := hPS hA Wp Wq P p F j hjr w a b ha hb Cb hCb hF hw.1
  set K : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
    TBB.normC nn w with hK
  have hae : (fun c => TBB.NP p nn F (j + 1) w (a ++ [(1, c)]) (b ++ [(1, c)])) =ᵐ[volume]
      fun c => (K : ℂ) * φ c := by
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx1.ae_ne_zero] with c hc
    rw [hφ c hc]
    unfold TBB.NP
    rw [nPt_append_one P _ a j ha hj c, nPt_append_one P _ b j hb hj c,
      Real.sqrt_mul (nPt_nonneg_loc P _ a j ha hjr), Real.sqrt_mul (nPt_nonneg_loc P _ b j hb hjr)]
    have hl := Real.mul_self_sqrt (levW_nonneg_low P j hj c)
    rw [hK]
    have : Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (KB.levW P (j + 1) c) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) * Real.sqrt (KB.levW P (j + 1) c)) / TBB.normC nn w =
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) / TBB.normC nn w *
          KB.levW P (j + 1) c := by
      calc _ = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) b) /
              TBB.normC nn w * (Real.sqrt (KB.levW P (j + 1) c) * Real.sqrt (KB.levW P (j + 1) c)) := by ring
        _ = _ := by rw [hl]
    rw [this]
    push_cast
    ring
  refine ⟨(hφi.const_mul (K : ℂ)).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_const_mul]
  have h0 := hφs 0
  simp only [P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_mul,
    Formalism.FourierDecayAlt.P.PBASM.waveG_zero_eq_self] at h0
  rw [h0]
  unfold TBB.NP
  congr 1
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨ha, hb⟩, dif_pos hjr]
  rfl

end

end Formalism.FourierDecayAlt.P.CutBP

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.CutBP.glFibre`.
-/
theorem Formalism.FourierDecayAlt.P.CutBP.low_level_fibre : Formalism.FourierDecayAlt.P.CutBP.GLFibre := Formalism.FourierDecayAlt.P.CutBP.glFibre
