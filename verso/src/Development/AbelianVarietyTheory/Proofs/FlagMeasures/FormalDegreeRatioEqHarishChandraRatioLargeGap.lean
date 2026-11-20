import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdDiffEqProdFactorial
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapDegreeRatio

/- English proof (translation)
Take `⟨c, hc, hF⟩` from `hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)`. Use `set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs`. Establish `hs0 : 0 < s` using `D.s.cdScale_pos _ _`. Establish `hs0' : (0 : ℝ) < s` using `by exact_mod_cast hs0`. Use `⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩` and prove the remaining obligations.

Take `⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩` from `hA`. Establish `hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l)` using `hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS`. Establish `hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l / s)`. Use `⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]`.

Establish `hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hFQ.1.ne'`. Establish `hcc : ((s : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hs0'.ne'`. Move the coercions through the operations in `at hd0 ⊢`. Clear the denominators using the available nonvanishing facts. Establish `: Nontrivial A.H` using `hDS.2.1`.

Take `⟨w, hw⟩` from `exists_ne (0 : A.H)`. Establish `hPd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP.1`. Establish `hQd : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1`. Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hPd`. Establish `hPP' : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hPd`.

Establish `hQQ : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q hQd`. Establish `hQQ' : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q hQd`. Set `u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ` to `⟨Q * P⁻¹, P * Q⁻¹, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ], by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩`. Set `a : Formalism.REAL.UJ (epsSH D.R)` to `⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩`. Establish `h1` using `GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by`.

Establish `e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹)` using `rfl`. Establish `e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q)`. Simplify using `only [Matrix.mul_assoc]`. Simplify using `only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw`. Establish `h2` using `GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw`.

Rewrite using `[← h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_eq_of_goodS (hH : GlobalTheory.GapIn.Hyp) (D : D7) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : LocW D.R.k D.R.rS) (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ),
      GoodS D l A → GapAtLeast (epsSH D.R) l h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h →
      A.deg = c * Formalism.QuantumDeterminants.fdegHC l := by
  obtain ⟨c, hc, hF⟩ := hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)
  set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs
  have hs0 : 0 < s := D.s.cdScale_pos _ _
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  refine ⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩
  obtain ⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩ := hA
  have hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l) :=
    hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS
  have hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q))
      (c * Formalism.QuantumDeterminants.fdegHC l / s) := by
    refine ⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]
    have hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hFQ.1.ne'
    have hcc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'.ne'
    push_cast at hd0 ⊢
    field_simp
  have : Nontrivial A.H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩
  have h1 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw
  rw [← h1, h2]
  ring

/- English proof (translation)
Introduce `hH D W l l' A A' h hA hA' hg hg' hok`. Take `⟨c, hc, hk⟩` from `deg_eq_of_goodS hH D`. Rewrite using `[hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]`. Conclude with `mul_div_mul_left _ _ hc.ne'`.
-/
theorem deg_ratio : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  intro hH D W l l' A A' h hA hA' hg hg' hok
  obtain ⟨c, hc, hk⟩ := deg_eq_of_goodS hH D
  rw [hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]
  exact mul_div_mul_left _ _ hc.ne'

end GlobalTheory.GapDegreeRatio
