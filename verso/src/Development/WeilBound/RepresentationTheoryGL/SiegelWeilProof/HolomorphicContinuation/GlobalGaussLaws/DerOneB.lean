import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneAbs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRangeStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneBH

variable {D : D7} {n : ℕ}

/- English proof (translation)
Simplify using `only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]`.
-/
theorem mt_mul' (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

/- English proof (translation)
Rewrite using `[mul_inv_rev, inv_inv, mt_mul', Matrix.mul_assoc]`.
-/
theorem shiftPt (V : HSp D) (x k : GA D V) (y : Mx D V.rank n) :
    HMul.hMul (mt V (x * k⁻¹)⁻¹) y = HMul.hMul (mt V k) (HMul.hMul (mt V x⁻¹) y) := by
  rw [mul_inv_rev, inv_inv, mt_mul', Matrix.mul_assoc]

/- English proof (translation)
Introduce `γ hγ h`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by`. Take `⟨u, -, hu⟩` from `(GQ V).inv_mem hγ`. Conclude with `⟨u, (congrArg Units.val hu).symm⟩`. Set `e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E` to `⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩`.

Use `(tsum_congr fun ξ => ?_).trans (e.tsum_eq _)` and prove the remaining obligations. Establish `: mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹` using `by rw [mul_inv_rev]; rfl`. Use `show ‖φ (HMul.hMul (mt V (γ * h)⁻¹) (rat ξ))‖ₑ = ‖φ (HMul.hMul (mt V h⁻¹) (rat (u.1 * ξ)))‖ₑ`. Rewrite using `[this, hu, Matrix.mul_assoc, ← rat_mul]`.
-/
theorem leftInv_absTheta (V : HSp D) (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : mt V (γ * h)⁻¹ = mt V h⁻¹ * mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show ‖φ (HMul.hMul (mt V (γ * h)⁻¹) (rat ξ))‖ₑ = ‖φ (HMul.hMul (mt V h⁻¹) (rat (u.1 * ξ)))‖ₑ
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

section Quot

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absTheta_eq (φ : Mx D V.rank n → ℂ) (y : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V φ y =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖φ (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) (rat ξ : Mx D V.rank n))‖ₑ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absThetaInt_eq (φ : Mx D V.rank n → ℂ) :
    GlobalTheory.SiegelFormula.absThetaInt V ν φ = ∫⁻ q, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ) q ∂autMeasure V ν := rfl

/- English proof (translation)
Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Rewrite using `[autMeasure, integral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]`. Conclude with `integral_congr_ae (.of_forall fun x => hf.descend_mk x)`.
-/
theorem int_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) :
    ∫ q, descend (GQ V) f q ∂autMeasure V ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, integral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact integral_congr_ae (.of_forall fun x => hf.descend_mk x)

/- English proof (translation)
Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Rewrite using `[autMeasure, lintegral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]`. Conclude with `lintegral_congr fun x => hf.descend_mk x`.
-/
theorem lint_q (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) :
    ∫⁻ q, descend (GQ V) f q ∂autMeasure V ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [autMeasure, lintegral_quotMeasure (isFundamentalDomain_stdDom (GQ V) ν)]
  exact lintegral_congr fun x => hf.descend_mk x

/- English proof (translation)
Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Rewrite `hi`, the goal using `[← memLp_one_iff_integrable]`. Use `(memLp_quotMeasure_iff (isFundamentalDomain_stdDom (GQ V) ν)).1 hi` as an intermediate fact. Rewrite `this` using `[hf.lift_descend]`. Then use the resulting hypothesis.
-/
theorem intg_q (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν)) :
    Integrable f (ν.restrict (stdDom (GQ V))) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  rw [← memLp_one_iff_integrable] at hi ⊢
  have := (memLp_quotMeasure_iff (isFundamentalDomain_stdDom (GQ V) ν)).1 hi
  rwa [hf.lift_descend] at this

/- English proof (translation)
Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Proceed by induction on `q using Quotient.inductionOn with`. Consider the case `h x => exact ((hf.mul_right k).descend_mk x).trans (hf.descend_mk (x * k)).symm`.
-/
theorem desc_r {X' : Type} (f : GA D V → X') (hf : LeftInv (GQ V) f) (k : GA D V) (q : GlobalTheory.AutomorphicL2Unitary.Quot (GQ V)) :
    descend (GQ V) (fun x => f (x * k)) q = descend (GQ V) f (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k q) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  induction q using Quotient.inductionOn with
  | h x => exact ((hf.mul_right k).descend_mk x).trans (hf.descend_mk (x * k)).symm

/- English proof (translation)
Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Use `haveI : ν.IsMulRightInvariant := GlobalTheory.RegSch.Ibp.isMulRightInvariant ν`. Conclude with `measurePreserving_rmul k`.
-/
theorem mp_r (k : GA D V) :
    MeasurePreserving (GlobalTheory.ThetaInv.rmulEquiv (GQ V) k) (autMeasure V ν) (autMeasure V ν) := by
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : ν.IsMulRightInvariant := GlobalTheory.RegSch.Ibp.isMulRightInvariant ν
  exact measurePreserving_rmul k

/- English proof (translation)
Rewrite using `[← int_q V ν _ (hf.mul_right k), ← int_q V ν f hf]`. Simplify using `only [desc_r V f hf k]`. Conclude with `(mp_r V ν k).integral_comp' (descend (GQ V) f)`.
-/
theorem int_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫ x in stdDom (GQ V), f (x * k) ∂ν = ∫ x in stdDom (GQ V), f x ∂ν := by
  rw [← int_q V ν _ (hf.mul_right k), ← int_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).integral_comp' (descend (GQ V) f)

/- English proof (translation)
Rewrite using `[← lint_q V ν _ (hf.mul_right k), ← lint_q V ν f hf]`. Simplify using `only [desc_r V f hf k]`. Conclude with `(mp_r V ν k).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (descend (GQ V) f)`.
-/
theorem lint_r (f : GA D V → ℝ≥0∞) (hf : LeftInv (GQ V) f) (k : GA D V) :
    ∫⁻ x in stdDom (GQ V), f (x * k) ∂ν = ∫⁻ x in stdDom (GQ V), f x ∂ν := by
  rw [← lint_q V ν _ (hf.mul_right k), ← lint_q V ν f hf]
  simp only [desc_r V f hf k]
  exact (mp_r V ν k).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (descend (GQ V) f)

/- English proof (translation)
Use `intg_q V ν _ (hf.mul_right k) ?_` and prove the remaining obligations. Establish `e : descend (GQ V) (fun x => f (x * k)) = descend (GQ V) f ∘ GlobalTheory.ThetaInv.rmulEquiv (GQ V) k`. Use function extensionality and compare the values at `fun q => desc_r V f hf k q`. Rewrite using `[e]`. Conclude with `((mp_r V ν k).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi`.
-/
theorem intg_r (f : GA D V → ℂ) (hf : LeftInv (GQ V) f) (hi : Integrable (descend (GQ V) f) (autMeasure V ν))
    (k : GA D V) : Integrable (fun x => f (x * k)) (ν.restrict (stdDom (GQ V))) := by
  refine intg_q V ν _ (hf.mul_right k) ?_
  have e : descend (GQ V) (fun x => f (x * k)) = descend (GQ V) f ∘ GlobalTheory.ThetaInv.rmulEquiv (GQ V) k :=
    funext fun q => desc_r V f hf k q
  rw [e]
  exact ((mp_r V ν k).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi

end Quot

section Kernel

variable (V : HSp D)

def tK (φ : Mx D V.rank n → ℂ) (x : GA D V) : ℂ :=
  ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, φ (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n))

def FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) : ℂ :=
  φ (HMul.hMul (Formalism.L2.Theta.mt V (hh t)) (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)))

/- English proof (translation)
Introduce `γ hγ h`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ⁻¹ = rat u.1 := by`. Take `⟨u, -, hu⟩` from `(GQ V).inv_mem hγ`. Conclude with `⟨u, (congrArg Units.val hu).symm⟩`. Set `e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E` to `⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc], fun ξ => by simp [← Matrix.mul_assoc]⟩`.

Use `(tsum_congr fun ξ => ?_).trans (e.tsum_eq _)` and prove the remaining obligations. Establish `: Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹` using `by rw [mul_inv_rev]; rfl`. Use `show φ (HMul.hMul (Formalism.L2.Theta.mt V (γ * h)⁻¹) (rat ξ)) = φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (rat (u.1 * ξ)))`. Rewrite using `[this, hu, Matrix.mul_assoc, ← rat_mul]`.
-/
theorem leftInv_tK (φ : Mx D V.rank n → ℂ) : LeftInv (GQ V) (tK V φ) := by
  intro γ hγ h
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin V.rank) D.host.E, Formalism.L2.Theta.mt V γ⁻¹ = rat u.1 := by
    obtain ⟨u, -, hu⟩ := (GQ V).inv_mem hγ
    exact ⟨u, (congrArg Units.val hu).symm⟩
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => u.1 * ξ, fun ξ => (u⁻¹).1 * ξ, fun ξ => by simp [← Matrix.mul_assoc],
      fun ξ => by simp [← Matrix.mul_assoc]⟩
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq _)
  have : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  show φ (HMul.hMul (Formalism.L2.Theta.mt V (γ * h)⁻¹) (rat ξ)) = φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (rat (u.1 * ξ)))
  rw [this, hu, Matrix.mul_assoc, ← rat_mul]

/- English proof (translation)
The claim follows from `tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]`.
-/
theorem tsum_FF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, FF V φ hh x t ξ = tK V φ (x * (hh t)⁻¹) :=
  tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

/- English proof (translation)
Rewrite using `[absTheta_eq]`. Conclude with `tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]`.
-/
theorem tsum_nFF (φ : Mx D V.rank n → ℂ) (hh : ℝ → GA D V) (x : GA D V) (t : ℝ) :
    ∑' ξ, ‖FF V φ hh x t ξ‖ₑ = GlobalTheory.SiegelFormula.absTheta V φ (x * (hh t)⁻¹) := by
  rw [absTheta_eq]
  exact tsum_congr fun ξ => by simp only [FF]; rw [shiftPt]

end Kernel

end PositivityTheory.Rg.Sw.Glob.DerOneBH

namespace PositivityTheory.Rg.Sw.Glob

open DerOneBH

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX Θ Θ' hΘ'`. Take `⟨h0, -, hΦ⟩` from `hC D n V θ τ s ε fr X hx.hθ hx.hs hx.hfr hX`. Use `haveI : ν.IsHaarMeasure := hx.hν`. Use `haveI : BorelSpace (GA D V) := ⟨rfl⟩`. Use `haveI : IsFiniteMeasure (autMeasure V ν) := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure ν`.

Use `haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)`. Use `haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) := inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))`. Use `letI : MeasurableSpace (Matrix (Fin V.rank) (Fin n) D.host.E) := ⊤`. Use `haveI : MeasurableSingletonClass (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun _ => trivial⟩`. Use `haveI : IsFiniteMeasure (ν.restrict (stdDom (GQ V))) := ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ (isFundamentalDomain_stdDom (GQ V) ν)]`.

Conclude with `measure_lt_top _ _⟩`. Establish `hT : ∀ Φ : schwartzA θ V.rank n, theta ω Φ 1 = tK V Φ.1` using `fun Φ => by`. Use function extensionality and compare the values at `x`. Simplify using `only [theta, map_one, Module.End.one_apply, tK]`. Establish `hfinA : ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤` using `fun Φ => hW D n V hx.hn (Or.inr hx.hr.2.2) θ hx.hθ ν hx.hν Φ`.

Establish `hfinA' : ∀ (Φ : schwartzA θ V.rank n) (k : GA D V), ∫⁻ x in stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V Φ.1 (x * k) ∂ν = GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1` using `fun Φ k => by`. Rewrite using `[lint_r V ν _ (leftInv_absTheta V Φ.1) k, ← lint_q V ν _ (leftInv_absTheta V Φ.1), absThetaInt_eq]`. Establish `hintT : ∀ Φ : schwartzA θ V.rank n, Integrable (descend (GQ V) (tK V Φ.1)) (autMeasure V ν)` using `fun Φ => by`. Rewrite using `[← hT]`. Conclude with `GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hx.hn hx.hr.2.2 θ hx.hθ ω ν hx.hν Φ 1`.

Establish `hhinv0 : (DerOneH.hhT θ V τ fr X 0)⁻¹ = 1` using `by rw [h0, inv_one]`. Establish `hmeasA : ∀ (Φ : schwartzA θ V.rank n) (t : ℝ), Measurable fun x : GA D V => ∑' ξ, ‖FF V Φ.1 (DerOneH.hhT θ V τ fr X) x t ξ‖ₑ` using `fun Φ t => Measurable.ennreal_tsum fun ξ => (((hΦ Φ).1 (rat ξ : Mx D V.rank n)).comp (Continuous.prodMk continuous_id continuous_const)).enorm.measurable`. Establish `key` using `DerOneAbsH.integral_deriv_zero (ν.restrict (stdDom (GQ V))) (FF V Θ.1 (DerOneH.hhT θ V τ fr X)) (FF V Θ'.1 (DerOneH.hhT θ V τ fr X)) (fun x ξ t _ => by`. Use `(hΦ Θ).2 (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)) t` as an intermediate fact. Rewrite `this` using `[← hΘ']`.

Conclude with `this)`. Use the proof step `(fun x ξ => by`. Establish `h` using `((hΦ Θ').1 (rat ξ : Mx D V.rank n)).comp (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (x, t))`. Conclude with `h)`. Use the proof step `(fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).aestronglyMeasurable)`.

Use the proof step `(by`. Establish `hm : Measurable fun p : GA D V × ℝ => ∑' ξ, ‖FF V Θ'.1 (DerOneH.hhT θ V τ fr X) p.1 p.2 ξ‖ₑ` using `Measurable.ennreal_tsum fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).enorm.measurable`. Rewrite using `[lintegral_prod_symm _ hm.aemeasurable]`. Simplify using `only [tsum_nFF, hfinA']`. Rewrite using `[lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]`.

Simplify using `only [sub_zero, ENNReal.ofReal_one, mul_one]`. Conclude with `(hfinA Θ').ne)`. Use the proof step `(by`. Establish `h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖ₑ ∂ν ≠ ⊤`. Simplify using `only [tsum_nFF, hfinA']`.

Conclude with `(hfinA Θ).ne`. Use `filter_upwards [ae_lt_top' (hmeasA Θ 0).aemeasurable h1] with x hx'`. Establish `hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖₊` using `ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne`. Conclude with `NNReal.summable_coe.2 hs)`. Use the proof step `(by`.

Establish `h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖ₑ ∂ν ≠ ⊤`. Simplify using `only [tsum_nFF, hfinA']`. Conclude with `(hfinA Θ).ne`. Use `filter_upwards [ae_lt_top' (hmeasA Θ 1).aemeasurable h1] with x hx'`. Establish `hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖₊` using `ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne`.

Conclude with `NNReal.summable_coe.2 hs)`. Use the proof step `(by`. Simplify using `only [tsum_FF, hhinv0, mul_one]`. Conclude with `intg_q V ν _ (leftInv_tK V Θ.1) (hintT Θ))`. Use the proof step `(by`.

Simplify using `only [tsum_FF]`. Conclude with `intg_r V ν _ (leftInv_tK V Θ.1) (hintT Θ) _)`. Use the proof step `(by`. Simplify using `only [tsum_FF, hhinv0, mul_one]`. Conclude with `int_r V ν _ (leftInv_tK V Θ.1) _)`.

Use the proof step `(fun t _ => by`. Simplify using `only [tsum_FF, hhinv0, mul_one]`. Conclude with `int_r V ν _ (leftInv_tK V Θ'.1) _)`. Simplify using `only [tsum_FF, hhinv0, mul_one] at key`. Rewrite using `[thetaInt, hT, average_eq, int_q V ν _ (leftInv_tK V Θ'.1), key, smul_zero]`.
-/
theorem derivOne_of (hW : GlobalTheory.Published.WeilThetaConvergence) (hC : DerOneH.CurveSt) : DerivOne := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX Θ Θ' hΘ'
  obtain ⟨h0, -, hΦ⟩ := hC D n V θ τ s ε fr X hx.hθ hx.hs hx.hfr hX
  haveI : ν.IsHaarMeasure := hx.hν
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (autMeasure V ν) := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure ν
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  letI : MeasurableSpace (Matrix (Fin V.rank) (Fin n) D.host.E) := ⊤
  haveI : MeasurableSingletonClass (Matrix (Fin V.rank) (Fin n) D.host.E) := ⟨fun _ => trivial⟩
  haveI : IsFiniteMeasure (ν.restrict (stdDom (GQ V))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ (isFundamentalDomain_stdDom (GQ V) ν)]
        exact measure_lt_top _ _⟩
  have hT : ∀ Φ : schwartzA θ V.rank n, theta ω Φ 1 = tK V Φ.1 := fun Φ => by
    funext x
    simp only [theta, map_one, Module.End.one_apply, tK]
  have hfinA : ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤ :=
    fun Φ => hW D n V hx.hn (Or.inr hx.hr.2.2) θ hx.hθ ν hx.hν Φ
  have hfinA' : ∀ (Φ : schwartzA θ V.rank n) (k : GA D V),
      ∫⁻ x in stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V Φ.1 (x * k) ∂ν = GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 :=
    fun Φ k => by
      rw [lint_r V ν _ (leftInv_absTheta V Φ.1) k, ← lint_q V ν _ (leftInv_absTheta V Φ.1), absThetaInt_eq]
  have hintT : ∀ Φ : schwartzA θ V.rank n, Integrable (descend (GQ V) (tK V Φ.1)) (autMeasure V ν) := fun Φ => by
    rw [← hT]; exact GlobalTheory.T.integrable_standardPair_theta_weilRange hW D n V hx.hn hx.hr.2.2 θ hx.hθ ω ν hx.hν Φ 1
  have hhinv0 : (DerOneH.hhT θ V τ fr X 0)⁻¹ = 1 := by rw [h0, inv_one]
  have hmeasA : ∀ (Φ : schwartzA θ V.rank n) (t : ℝ), Measurable fun x : GA D V =>
      ∑' ξ, ‖FF V Φ.1 (DerOneH.hhT θ V τ fr X) x t ξ‖ₑ :=
    fun Φ t => Measurable.ennreal_tsum fun ξ =>
      (((hΦ Φ).1 (rat ξ : Mx D V.rank n)).comp (Continuous.prodMk continuous_id continuous_const)).enorm.measurable
  have key := DerOneAbsH.integral_deriv_zero (ν.restrict (stdDom (GQ V)))
    (FF V Θ.1 (DerOneH.hhT θ V τ fr X)) (FF V Θ'.1 (DerOneH.hhT θ V τ fr X))
    (fun x ξ t _ => by
      have := (hΦ Θ).2 (HMul.hMul (Formalism.L2.Theta.mt V x⁻¹) (rat ξ : Mx D V.rank n)) t
      rw [← hΘ'] at this
      exact this)
    (fun x ξ => by
      have h := ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).comp
        (continuous_const.prodMk continuous_id : Continuous fun t : ℝ => (x, t))
      exact h)
    (fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).aestronglyMeasurable)
    (by
      have hm : Measurable fun p : GA D V × ℝ => ∑' ξ, ‖FF V Θ'.1 (DerOneH.hhT θ V τ fr X) p.1 p.2 ξ‖ₑ :=
        Measurable.ennreal_tsum fun ξ => ((hΦ Θ').1 (rat ξ : Mx D V.rank n)).enorm.measurable
      rw [lintegral_prod_symm _ hm.aemeasurable]
      simp only [tsum_nFF, hfinA']
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      simp only [sub_zero, ENNReal.ofReal_one, mul_one]
      exact (hfinA Θ').ne)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 0).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 0 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      have h1 : ∫⁻ x in stdDom (GQ V), ∑' ξ, ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖ₑ ∂ν ≠ ⊤ := by
        simp only [tsum_nFF, hfinA']
        exact (hfinA Θ).ne
      filter_upwards [ae_lt_top' (hmeasA Θ 1).aemeasurable h1] with x hx'
      have hs : Summable fun ξ => ‖FF V Θ.1 (DerOneH.hhT θ V τ fr X) x 1 ξ‖₊ :=
        ENNReal.tsum_coe_ne_top_iff_summable.1 hx'.ne
      exact NNReal.summable_coe.2 hs)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact intg_q V ν _ (leftInv_tK V Θ.1) (hintT Θ))
    (by
      simp only [tsum_FF]
      exact intg_r V ν _ (leftInv_tK V Θ.1) (hintT Θ) _)
    (by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ.1) _)
    (fun t _ => by
      simp only [tsum_FF, hhinv0, mul_one]
      exact int_r V ν _ (leftInv_tK V Θ'.1) _)
  simp only [tsum_FF, hhinv0, mul_one] at key
  rw [thetaInt, hT, average_eq, int_q V ν _ (leftInv_tK V Θ'.1), key, smul_zero]

end PositivityTheory.Rg.Sw.Glob
