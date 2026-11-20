import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hQ : MeasurableSet (MA.Qset r TT)` using `(MA.Qset_open r TT).measurableSet`. Rewrite using `[MA.mu0, lintegral_subtype_comap hQ (fun x => H x), restrict_withDensity hQ]`. Conclude with `lintegral_withDensity_le_lintegral_mul _ Formalism.FourierDecayAlt.P.MAx2.Adj.density_measurable H`.
-/
theorem lintegral_base_measure_le {r : ℕ} {TT : ℝ} (H : MA.E r → ENNReal) :
    ∫⁻ q : MA.Qp r TT, H q.1 ∂MA.mu0 r TT ≤ ∫⁻ x in MA.Qset r TT, MA.dens0 x * H x := by
  have hQ : MeasurableSet (MA.Qset r TT) := (MA.Qset_open r TT).measurableSet
  rw [MA.mu0, lintegral_subtype_comap hQ (fun x => H x), restrict_withDensity hQ]
  exact lintegral_withDensity_le_lintegral_mul _ Formalism.FourierDecayAlt.P.MAx2.Adj.density_measurable H

/- English proof (translation)
Establish `ha : (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Establish `hb : (0 : ℝ) ≤ k` using `Nat.cast_nonneg _`. Establish `hn : nDim k r = 2 * (r : ℝ) + k + 1` using `by unfold nDim; push_cast; ring`. Unfold `B.AB`. Rewrite using `[hn]`.

Use polynomial arithmetic with `[sq_nonneg (r : ℝ), mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) ha, mul_nonneg (mul_nonneg ha ha) hb, mul_nonneg (mul_nonneg ha hb) ha]`.
-/
theorem jd_AB_le (k r : ℕ) : B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 2 * nDim k r := by
  have ha : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  unfold B.AB
  rw [hn]
  nlinarith [sq_nonneg (r : ℝ), mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) ha, mul_nonneg (mul_nonneg ha ha) hb,
    mul_nonneg (mul_nonneg ha hb) ha]

/- English proof (translation)
Use `⟨3, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr A hA F hCk hCC hFF π`. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Use `set Db := (T v).base with hDb`. Establish `hT : Tz S.G.k S.G.r Db.z = S.T` using `hPl.2.2.2.1`.

Establish `hT' : Tz S.G.k S.G.r Db.z' = S.T'` using `hPl.2.2.2.2.1`. Establish `hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT` using `by rw [hT, hT']; rfl`. Establish `hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT)` using `(MA.Qset_open _ _).measurableSet`. Establish `hAB : B.AB S.G.k S.G.r ≤ A` using `(jd_AB_le S.G.k S.G.r).trans hA`. Take `⟨c0, -, -, hB1, -⟩` from `Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A hAB`.

Take `⟨C, hC⟩` from `hB1`. Take `⟨c4, hc4⟩` from `hCC 4`. Establish `hN : B.normSq Db F ≠ ⊤` using `(hC F F c4 c4 (hCC 5) (hCC 5) hc4 hc4).1`. Unfold `B.normSq jNormSq at hN`. Establish `hsm` using `Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr (B.JF Db F) hFF π`.

Establish `hval` using `Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm`. Use `⟨((jd_evQ_meas _ _).norm).pow 2, ?_⟩` and prove the remaining obligations. Use `(hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_` and prove the remaining obligations. Use `set H : MA.E S.G.r → ENNReal := fun x => ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH`. Establish `p1 : ∀ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2) ≤ H q.1`.

Introduce `q`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `hq : MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q = ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))` using `congrFun hval q`. Rewrite using `[hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Establish `hw` using `Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2`.

Rewrite using `[Real.sq_sqrt hw.le]`. Use `mul_le_mul_of_nonneg_left ?_ hw.le` and prove the remaining obligations. Establish `he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1`. Establish `h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ)`. Simplify using `using (hFr.2 q.1.2 q.2.2).2.1 π π`.

Rewrite `h1` using `[inner_self_eq_norm_sq_to_K]`. Establish `h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_pow, Complex.ofReal_one]`. Conclude with `h1`. Establish `h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1` using `Complex.ofReal_injective h2'`.

Use polynomial arithmetic with `[norm_nonneg (B.hsVec (e π q.1.2))]`. Establish `hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤ ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖` using `(norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hi 2`. Establish `p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤ ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2)`. Introduce `x hx`.

Establish `hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x)`. Unfold `MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]`. Establish `hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x` using `Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)`. Establish `hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT`.

Establish `hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2`. Rewrite using `[hTT]`. Conclude with `le_of_lt hx.2`. Unfold `bcWeight`. Rewrite using `[if_pos hle]`.

Unfold `Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq`. Rewrite using `[hTT, ← mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hM : 2 ≤ MA.Mdim S.G.k S.G.r l`.

Use `l.isLt` as an intermediate fact. Simplify using `only [MA.Mdim]`. Use linear arithmetic over natural numbers and integers. Establish `hn : Complex.normSq (x.1 l) ≠ 0` using `(Complex.normSq_pos.2 (hx.1 l)).ne'`. Establish `e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l` using `rfl`.

Rewrite using `[e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega, pow_succ]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem transfer_square_integrable_holds : TransferSquareIntegrable := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr A hA F hCk hCC hFF π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  have hAB : B.AB S.G.k S.G.r ≤ A := (jd_AB_le S.G.k S.G.r).trans hA
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hCC 4
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hCC 5) (hCC 5) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr (B.JF Db F) hFF π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  refine ⟨((jd_evQ_meas _ _).norm).pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT,
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2) ≤ H q.1 := by
    intro q
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2)
          ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT
        ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          lintegral_mono p1
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end

end Formalism.FourierDecayAlt.P.CutMP
