import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.ThetaIrred

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

/- English proof (translation)
Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Take `⟨Cf, hCf⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hf`. Take `⟨Cg, hCg⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hg`. Use `Integrable.of_bound (hf.cont.star.mul (hq.mul hg.cont)).aestronglyMeasurable (Cf * (Cq * Cg)) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_star]`. Establish `a0 : 0 ≤ Cq` using `(norm_nonneg _).trans (hCq x)`. Establish `b0 : 0 ≤ Cf` using `(norm_nonneg _).trans (hCf x)`. Conclude with `mul_le_mul (hCf x) (mul_le_mul (hCq x) (hCg x) (norm_nonneg _) a0) (by positivity) b0`.
-/
theorem integrable_star_mul (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {f g q : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (hq : Continuous q)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    Integrable (fun x => star (f x) * (q x * g x)) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨Cf, hCf⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hf
  obtain ⟨Cg, hCg⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hg
  refine Integrable.of_bound (hf.cont.star.mul (hq.mul hg.cont)).aestronglyMeasurable (Cf * (Cq * Cg))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_star]
  have a0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq x)
  have b0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf x)
  exact mul_le_mul (hCf x) (mul_le_mul (hCq x) (hCg x) (norm_nonneg _) a0) (by positivity) b0

/- English proof (translation)
Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hth` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1`. Take `⟨Ch, hCh⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hh`. Take `⟨Ck, hCk⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hk`.

Establish `ch0 : 0 ≤ Ch` using `(norm_nonneg _).trans (hCh 0)`. Establish `ck0 : 0 ≤ Ck` using `(norm_nonneg _).trans (hCk 0)`. Use `set I := ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ with hIdef`. Establish `hint` using `integrable_star_mul hψ h1 hh hk hq hCq`. Establish `key : ∀ δ : ℝ, 0 < δ → ‖I‖ ≤ δ * (Ch * Ck)`.

Introduce `δ hδ`. Take `⟨s, c, hsc⟩` from `GlobalTheory.ThetaSchurBdd.trig_approx hψ hq hqp hδ`. Establish `hpk` using `GlobalTheory.ThetaSchurBdd.trig_mul_eq s c hk`. Establish `hsum : ∀ x, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) = ∑ a ∈ s, c a * (star (h x) * heisO ψ S T a k x)`. Introduce `x`.

Use `congrFun hpk x` as an intermediate fact. Rewrite using `[this, Finset.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint_a : ∀ a ∈ s, Integrable (fun x => c a * (star (h x) * heisO ψ S T a k x)) (μ.restrict 𝓕)`. Introduce `a _`. Use `integrable_star_mul hψ h1 hh (hth a k hk) (q := fun _ => (1 : ℂ)) continuous_const (Cq := 1) (fun _ => by simp)` as an intermediate fact. Simplify using `only [one_mul] at this`. Conclude with `this.const_mul (c a)`.

Establish `hP : ∫ x in 𝓕, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) ∂μ = 0`. Repeatedly rewrite using `[hsum]`. Rewrite using `[integral_finset_sum s hint_a]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`.

Use `horth a a.2` as an intermediate fact. Unfold `thetaIP at this`. Rewrite using `[this, mul_zero]`. Establish `hPint : Integrable (fun x => star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) (μ.restrict 𝓕)`. Repeatedly rewrite using `[hsum]`.

Conclude with `integrable_finset_sum s hint_a`. Establish `hdiff : I = ∫ x in 𝓕, (star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) ∂μ`. Rewrite using `[integral_sub hint hPint, hP, sub_zero]`. Rewrite using `[hdiff]`. Establish `hb : ∀ᵐ x ∂(μ.restrict 𝓕), ‖star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)‖ ≤ δ * (Ch * Ck)`.

Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations. Rewrite using `[show star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) = star (h x) * ((q x - ∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) by ring]`. Rewrite using `[norm_mul, norm_mul, norm_star]`. Establish `e1` using `hsc x`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_integral_le_of_norm_le_const hb).trans ?_` and prove the remaining obligations. Rewrite using `[measureReal_def, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, mul_one]`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖I‖` using `norm_pos_iff.2 hne`. Establish `hM : 0 < Ch * Ck + 1` using `by positivity`.

Use `key (‖I‖ / (Ch * Ck + 1)) (div_pos hpos hM)` as an intermediate fact. Rewrite `this` using `[div_mul_eq_mul_div, le_div_iff₀ hM]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem orth_periodic (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0)
    {q : WO S T → ℂ} (hq : Continuous q) (hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x)
    {Cq : ℝ} (hCq : ∀ x, ‖q x‖ ≤ Cq) :
    ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ = 0 := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  have ck0 : 0 ≤ Ck := (norm_nonneg _).trans (hCk 0)
  set I := ∫ x in 𝓕, star (h x) * (q x * k x) ∂μ with hIdef
  have hint := integrable_star_mul hψ h1 hh hk hq hCq
  have key : ∀ δ : ℝ, 0 < δ → ‖I‖ ≤ δ * (Ch * Ck) := by
    intro δ hδ
    obtain ⟨s, c, hsc⟩ := GlobalTheory.ThetaSchurBdd.trig_approx hψ hq hqp hδ
    have hpk := GlobalTheory.ThetaSchurBdd.trig_mul_eq s c hk
    have hsum : ∀ x, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        ∑ a ∈ s, c a * (star (h x) * heisO ψ S T a k x) := by
      intro x
      have := congrFun hpk x
      rw [this, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    have hint_a : ∀ a ∈ s, Integrable (fun x => c a * (star (h x) * heisO ψ S T a k x)) (μ.restrict 𝓕) := by
      intro a _
      have := integrable_star_mul hψ h1 hh (hth a k hk) (q := fun _ => (1 : ℂ)) continuous_const (Cq := 1)
        (fun _ => by simp)
      simp only [one_mul] at this
      exact this.const_mul (c a)
    have hP : ∫ x in 𝓕, star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) ∂μ = 0 := by
      simp_rw [hsum]
      rw [integral_finset_sum s hint_a]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [integral_const_mul]
      have := horth a a.2
      unfold thetaIP at this
      rw [this, mul_zero]
    have hPint : Integrable (fun x => star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) (μ.restrict 𝓕) := by
      simp_rw [hsum]
      exact integrable_finset_sum s hint_a
    have hdiff : I = ∫ x in 𝓕, (star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)) ∂μ := by
      rw [integral_sub hint hPint, hP, sub_zero]
    rw [hdiff]
    have hb : ∀ᵐ x ∂(μ.restrict 𝓕), ‖star (h x) * (q x * k x) -
        star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x)‖ ≤ δ * (Ch * Ck) := by
      refine Filter.Eventually.of_forall fun x => ?_
      rw [show star (h x) * (q x * k x) - star (h x) * ((∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) =
        star (h x) * ((q x - ∑ a ∈ s, c a * ψ (symplO S T x a)) * k x) by ring]
      rw [norm_mul, norm_mul, norm_star]
      have e1 := hsc x
      calc ‖h x‖ * (‖q x - ∑ a ∈ s, c a * ψ (symplO S T x a)‖ * ‖k x‖) ≤ Ch * (δ * Ck) :=
            mul_le_mul (hCh x) (mul_le_mul e1 (hCk x) (norm_nonneg _) hδ.le) (by positivity) ch0
        _ = δ * (Ch * Ck) := by ring
    refine (norm_integral_le_of_norm_le_const hb).trans ?_
    rw [measureReal_def, Measure.restrict_apply_univ, h1, ENNReal.toReal_one, mul_one]
  by_contra hne
  have hpos : 0 < ‖I‖ := norm_pos_iff.2 hne
  have hM : 0 < Ch * Ck + 1 := by positivity
  have := key (‖I‖ / (Ch * Ck + 1)) (div_pos hpos hM)
  rw [div_mul_eq_mul_div, le_div_iff₀ hM] at this
  nlinarith

/- English proof (translation)
Establish `h1 : μ 𝓕 = 1` using `hcv.2.2`. Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Take `⟨Ch, hCh⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hh`. Take `⟨Ck, hCk⟩` from `GlobalTheory.ThetaSchurBdd.exists_bound hψ hk`. Establish `ch0 : 0 ≤ Ch` using `(norm_nonneg _).trans (hCh 0)`.

Use `set q : WO S T → ℂ := fun x => h x * star (k x) with hq`. Establish `hqc : Continuous q` using `hh.cont.mul hk.cont.star`. Establish `hqb : ∀ x, ‖q x‖ ≤ Ch * Ck` using `fun x => by`. Rewrite using `[hq, norm_mul, norm_star]`. Conclude with `mul_le_mul (hCh x) (hCk x) (norm_nonneg _) ch0`.

Establish `hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x` using `fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hh hk hγ x`. Establish `hz` using `orth_periodic hψ h1 hh hk horth hqc hqp hqb`. Use `set F : WO S T → ℝ := fun x => ‖h x‖ ^ 2 * ‖k x‖ ^ 2 with hF`. Establish `hpt : ∀ x, star (h x) * (q x * k x) = ((F x : ℝ) : ℂ)`. Introduce `x`.

Rewrite using `[hq, hF, show star (h x) * (h x * star (k x) * k x) = (star (h x) * h x) * (star (k x) * k x) by ring]`. Simplify using `only [Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hint` using `integrable_star_mul hψ h1 hh hk hqc hqb`.

Rewrite `hz`, `hint` using `[hpt]`. Rewrite `hz` using `[integral_complex_ofReal, Complex.ofReal_eq_zero]`. Establish `hFi : Integrable F (μ.restrict 𝓕)`. Use `hint.re` as an intermediate fact. Simplify using `using this`.

Establish `hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0` using `(integral_eq_zero_iff_of_nonneg (fun x => by positivity) hFi).1 hz`. Establish `hf` using `GlobalTheory.ThetaSchurBdd.isTheta_star_mul_mul hψ hk hk hh`. Establish `h0 : nrm2 μ 𝓕 (fun x => star (k x) * k x * h x) = 0`. Unfold `nrm2`. Use `integral_eq_zero_of_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with y hy`. Establish `e : ‖star (k y) * k y * h y‖ ^ 2 = ‖k y‖ ^ 2 * F y`. Rewrite using `[hF, norm_mul, norm_mul, norm_star]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Pi.zero_apply, e, hy, mul_zero]`.

Use `congrFun (GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf h0) x` as an intermediate fact. Simplify using `only [Pi.zero_apply, mul_eq_zero, star_eq_zero, or_self] at this`. Conclude with `this.symm`.
-/
theorem pointwise (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕)
    {h k : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) (hk : IsThetaFunO ψ S T k)
    (horth : ∀ γ ∈ ratL T S, thetaIP μ 𝓕 h (heisO ψ S T γ k) = 0) (x : WO S T) :
    h x = 0 ∨ k x = 0 := by
  have h1 : μ 𝓕 = 1 := hcv.2.2
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨Ch, hCh⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hh
  obtain ⟨Ck, hCk⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hk
  have ch0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0)
  set q : WO S T → ℂ := fun x => h x * star (k x) with hq
  have hqc : Continuous q := hh.cont.mul hk.cont.star
  have hqb : ∀ x, ‖q x‖ ≤ Ch * Ck := fun x => by
    rw [hq, norm_mul, norm_star]
    exact mul_le_mul (hCh x) (hCk x) (norm_nonneg _) ch0
  have hqp : ∀ γ ∈ ratL T S, ∀ x, q (γ + x) = q x := fun γ hγ x =>
    GlobalTheory.ThetaSchur.prod_periodic hψ hh hk hγ x
  have hz := orth_periodic hψ h1 hh hk horth hqc hqp hqb
  set F : WO S T → ℝ := fun x => ‖h x‖ ^ 2 * ‖k x‖ ^ 2 with hF
  have hpt : ∀ x, star (h x) * (q x * k x) = ((F x : ℝ) : ℂ) := by
    intro x
    rw [hq, hF, show star (h x) * (h x * star (k x) * k x) = (star (h x) * h x) * (star (k x) * k x) by ring]
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hint := integrable_star_mul hψ h1 hh hk hqc hqb
  simp_rw [hpt] at hz hint
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hz
  have hFi : Integrable F (μ.restrict 𝓕) := by
    have := hint.re
    simpa using this
  have hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hFi).1 hz
  have hf := GlobalTheory.ThetaSchurBdd.isTheta_star_mul_mul hψ hk hk hh
  have h0 : nrm2 μ 𝓕 (fun x => star (k x) * k x * h x) = 0 := by
    unfold nrm2
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with y hy
    have e : ‖star (k y) * k y * h y‖ ^ 2 = ‖k y‖ ^ 2 * F y := by
      rw [hF, norm_mul, norm_mul, norm_star]; ring
    rw [Pi.zero_apply, e, hy, mul_zero]
  have := congrFun (GlobalTheory.ThetaSchurBdd.thetaFunction_eq_zero_of_meanSquare_zero hψ hcv hf h0) x
  simp only [Pi.zero_apply, mul_eq_zero, star_eq_zero, or_self] at this
  exact this.symm

end GlobalTheory.ThetaIrred

/- English proof (translation)
Introduce `D ψ S T hψ μ 𝓕 hcv h e hh he horth`. Establish `hth` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1`. Establish `hhh` using `(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1`. Establish `key : ∀ w x, h x = 0 ∨ heisO ψ S T w e x = 0`. Introduce `w x`.

Use `GlobalTheory.ThetaIrred.pointwise hψ hcv hh (hth w e he) (fun γ _ => ?_) x` and prove the remaining obligations. Rewrite using `[hhh γ w e]`. Unfold `thetaIP`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_left_comm (star (h _))]`. Rewrite using `[integral_const_mul]`.

Use `horth (γ + w)` as an intermediate fact. Unfold `thetaIP at this`. Rewrite using `[this, mul_zero]`. Distinguish the cases in `he0 : e = 0`. Conclude with `Or.inr he0`.

Use `left`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, e y ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Conclude with `he0 (funext hn)`.

Use function extensionality and compare the values at `x`. Break down `key (y - x) x with h0 | h0` into its components or cases. Conclude with `h0`. It suffices to derive a contradiction. Simplify using `only [heisO, add_sub_cancel] at h0`.

Break down `mul_eq_zero.1 h0 with h1 | h1` into its components or cases. Conclude with `GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _ h1`. Conclude with `hy h1`.
-/
theorem GlobalTheory.ThetaIrred.orth_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ w : WO S T, thetaIP μ 𝓕 h (heisO ψ S T w e) = 0) → h = 0 ∨ e = 0 := by
  intro D ψ S T hψ μ 𝓕 hcv h e hh he horth
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hhh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1
  have key : ∀ w x, h x = 0 ∨ heisO ψ S T w e x = 0 := by
    intro w x
    refine GlobalTheory.ThetaIrred.pointwise hψ hcv hh (hth w e he) (fun γ _ => ?_) x
    rw [hhh γ w e]
    unfold thetaIP
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (star (h _))]
    rw [integral_const_mul]
    have := horth (γ + w)
    unfold thetaIP at this
    rw [this, mul_zero]
  by_cases he0 : e = 0
  · exact Or.inr he0
  left
  obtain ⟨y, hy⟩ : ∃ y, e y ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact he0 (funext hn)
  funext x
  rcases key (y - x) x with h0 | h0
  · exact h0
  · exfalso
    simp only [heisO, add_sub_cancel] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact GlobalTheory.ThetaSchurBdd.psi_ne_zero hψ _ h1
    · exact hy h1
