import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaIntegrand

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaIntegrand

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold `_root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG`. Take `⟨c, h1, h2⟩` from `hG`. Conclude with `⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩`.
-/
private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
The claim follows from `measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)`.
-/
private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Use `(aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_` and prove the remaining obligations. Establish `h` using `_root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)`. Simplify using `only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h`. Conclude with `_root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h`.
-/
private theorem aestronglyMeasurable_indicator_hsVec_JF (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_Qset_iff_zero_lt_bcWeight (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
/- English proof (translation)
Distinguish the cases in `hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs`. Rewrite using `[Set.indicator_of_mem hq]`. Establish `hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0` using `le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)`. Rewrite using `[hw, zero_mul, zero_mul]`.
-/
private theorem bcWeight_mul_eq_bcWeight_mul_indicator (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {β : Type} [Zero β] (Φ : β → ℝ)
    (hΦ : Φ 0 = 0) (u : (Fin r → ℂ) × ℂ → β) (q : (Fin r → ℂ) × ℂ) :
    _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ (u q) =
      _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator u q) := by
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · rw [Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    rw [hw, zero_mul, zero_mul]

open Filter Topology MeasureTheory in

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ Bs A X F hA hX hF`. Take `⟨-, -, -, ⟨C, hC⟩, -⟩` from `_root_.Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq Bs A hA`. Take `⟨cF, hcF⟩` from `exists_CCle_four_of_inCC_five hF`. Take `⟨cX, hcX⟩` from `exists_CCle_four_of_inCC_five hX`. Take `⟨hFF, hFX, -⟩` from `hC F X cF cX hF hX hcF hcX`.

Unfold `_root_.Formalism.FourierDecayAlt.B.normSq _root_.Formalism.QuantumDeterminants.jNormSq at hFF hFX`. Use `set w := fun q => _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q with hw`. Use `set uF := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huF`. Use `set uX := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huX`. Establish `hmF : AEStronglyMeasurable uF volume` using `aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩))`.

Establish `hmX : AEStronglyMeasurable uX volume` using `aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩))`. Establish `hw0 : ∀ q, 0 ≤ w q` using `fun q => _root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q`. Establish `hfun : (fun q : (Fin r → ℂ) × ℂ => (w q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root …`. Use function extensionality and compare the values at `q`. Distinguish the cases in `hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs`.

Rewrite using `[huF, huX, Set.indicator_of_mem hq, Set.indicator_of_mem hq]`. Establish `hwq : w q = 0` using `le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (hw0 q)`. Rewrite using `[hwq, Complex.ofReal_zero, zero_mul, zero_mul]`. Establish `hFF' : ∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2) ≠ ⊤`. Use `ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFF` and prove the remaining obligations.

Conclude with `congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm`. Establish `hFX' : ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) ≠ ⊤`. Use `ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFX` and prove the remaining obligations. Conclude with `congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm`. Establish `hbound : ∀ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ ≤ ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2)`.

Introduce `q`. Rewrite using `[← ENNReal.ofReal_add (mul_nonneg (hw0 q) (sq_nonneg _)) (mul_nonneg (hw0 q) (sq_nonneg _)), ← ofReal_norm_eq_enorm]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 q)]`. Establish `h1` using `norm_inner_le_norm (𝕜 := ℂ) (uF q) (uX q)`.

Establish `h2 : ‖uF q‖ * ‖uX q‖ ≤ ‖uF q‖ ^ 2 + ‖uX q‖ ^ 2`. Use polynomial arithmetic with `[sq_nonneg (‖uF q‖ - ‖uX q‖), norm_nonneg (uF q), norm_nonneg (uX q)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 q)]`. Establish `haeF : AEMeasurable (fun q => ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) volume` using `ENNReal.measurable_ofReal.comp_aemeasurable ((_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aemeasurable.mul (hmF.norm.aemeasurable.pow_const 2))`. Rewrite using `[hfun]`.

Use `⟨(Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable.mul (hmF.inner hmX), ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_enorm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Integrable (fun q : (Fin r → ℂ) × ℂ => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs A X F hA hX hF
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := _root_.Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq Bs A hA
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  obtain ⟨hFF, hFX, -⟩ := hC F X cF cX hF hX hcF hcX
  unfold _root_.Formalism.FourierDecayAlt.B.normSq _root_.Formalism.QuantumDeterminants.jNormSq at hFF hFX
  set w := fun q => _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q with hw
  set uF := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huF
  set uX := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huX
  have hmF : AEStronglyMeasurable uF volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩))
  have hmX : AEStronglyMeasurable uX volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩))
  have hw0 : ∀ q, 0 ≤ w q := fun q => _root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q
  have hfun : (fun q : (Fin r → ℂ) × ℂ => (w q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) = fun q => (w q : ℂ) * inner ℂ (uF q) (uX q) := by
    funext q
    by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
    · rw [huF, huX, Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    · have hwq : w q = 0 :=
        le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (hw0 q)
      rw [hwq, Complex.ofReal_zero, zero_mul, zero_mul]
  have hFF' : ∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFF
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hFX' : ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFX
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hbound : ∀ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ ≤
      ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2) := by
    intro q
    rw [← ENNReal.ofReal_add (mul_nonneg (hw0 q) (sq_nonneg _)) (mul_nonneg (hw0 q) (sq_nonneg _)),
      ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 q)]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (uF q) (uX q)
    have h2 : ‖uF q‖ * ‖uX q‖ ≤ ‖uF q‖ ^ 2 + ‖uX q‖ ^ 2 := by
      nlinarith [sq_nonneg (‖uF q‖ - ‖uX q‖), norm_nonneg (uF q), norm_nonneg (uX q)]
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 q)]
  have haeF : AEMeasurable (fun q => ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aemeasurable.mul (hmF.norm.aemeasurable.pow_const 2))
  rw [hfun]
  refine ⟨(Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable.mul
    (hmF.inner hmX), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ
      ≤ ∫⁻ q, (ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2)) :=
        lintegral_mono hbound
    _ = (∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) + ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) :=
        lintegral_add_left' haeF _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hFF', lt_top_iff_ne_top.2 hFX'⟩
