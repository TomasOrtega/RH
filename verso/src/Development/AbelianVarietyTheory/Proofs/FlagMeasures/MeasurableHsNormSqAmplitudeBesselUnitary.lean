import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AmpMeas

/- English proof (translation)
Use `haveI : ProperSpace W := FiniteDimensional.proper ℂ W`. Use `letI : MeasurableSpace W := borel W`. Use `haveI : BorelSpace W := ⟨rfl⟩`. Use `hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS` as an intermediate fact. Establish `h2 : S.indicator f = S.piecewise f fun _ => (0 : W)`.

Apply the tactic sequence `funext x; by_cases hx : x ∈ S <;> simp [hx]`. Rewrite using `[h2]`. Conclude with `this.stronglyMeasurable`.
-/
theorem stronglyMeasurable_indicator_of_continuousOn {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {S : Set X}
    (hS : MeasurableSet S) {f : X → W} (hf : ContinuousOn f S) : StronglyMeasurable (S.indicator f) := by
  classical
  haveI : ProperSpace W := FiniteDimensional.proper ℂ W
  letI : MeasurableSpace W := borel W
  haveI : BorelSpace W := ⟨rfl⟩
  have := hf.measurable_piecewise (g := fun _ => (0 : W)) continuousOn_const hS
  have h2 : S.indicator f = S.piecewise f fun _ => (0 : W) := by
    funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h2]
  exact this.stronglyMeasurable

/- English proof (translation)
Unfold `hsNormSq hsInner`. Use `Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => ?_)` and prove the remaining obligations. Establish `: Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i)` using `(ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous`. Conclude with `this.inner this`.
-/
theorem continuous_hsNormSq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Continuous fun A : Wq →L[ℂ] Wp => hsNormSq A := by
  unfold hsNormSq hsInner
  refine Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => ?_)
  have : Continuous fun A : Wq →L[ℂ] Wp => A (stdOrthonormalBasis ℂ Wq i) :=
    (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous
  exact this.inner this

/- English proof (translation)
Introduce `k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'`. Use `haveI : SigmaFinite μG := hH.1`. Establish `hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r}` using `hcl`. Use `set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef`.

Establish `hS : MeasurableSet S` using `hcl'.measurableSet`. Establish `hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r`. Introduce `γ x hγ hx`. Establish `hs' : γᴴ * Hpk k r * γ = Hpk k r` using `hγ`. Establish `hx' : xᴴ * Hpk k r * x = Hpk k r` using `hx`.

Use `show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hs', hx']`.

Establish `hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r)` using `continuous_id`. Set `F : Mt k r × Mt k r → (Wq →L[ℂ] Wp)` to `fun p => (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))`. Establish `hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2`. Establish `h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1` using `(innerSL ℂ).continuous.comp continuous_fst`. Conclude with `((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)`.

Establish `h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S)` using `hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2`. Establish `h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S)` using `hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn fun p hp => hmul _ _ hp.1 hp.2`. Establish `hF : ContinuousOn F (S ×ˢ S)` using `hcont.comp_continuousOn (h1.prodMk h2)`. Establish `hsm : StronglyMeasurable ((S ×ˢ S).indicator F)` using `stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF`. Establish `hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG` using `hsm.integral_prod_right'`.

Establish `hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG)` using `(continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable`. Establish `hae : ∀ᵐ x ∂μG, x ∈ S` using `by rw [ae_iff]; exact hH.2.2.1`. Establish `heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) = S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG)`. Use `Set.indicator_congr fun γ hγ => ?_` and prove the remaining obligations. Unfold `ampJ`.

Use `congr 2`. Use `integral_congr_ae (hae.mono fun x hx => ?_)` and prove the remaining obligations. Establish `: (γ, x) ∈ S ×ˢ S` using `⟨hγ, hx⟩`. Simplify using `only [Set.indicator_of_mem this, F]`. Rewrite using `[heq]`.

Conclude with `hm.indicator hS`.
-/
theorem measurable_hsNormSq_ampJ : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  intro k r Wp _ _ _ _ Wq _ _ _ μG c Φ Φ' hH hΦ hΦ'
  haveI : SigmaFinite μG := hH.1
  have hcl : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hcl' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hcl
  set S : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ GG k r} with hSdef
  have hS : MeasurableSet S := hcl'.measurableSet
  have hmul : ∀ γ x : Mat k r, γ ∈ GG k r → x ∈ GG k r → γ * x ∈ GG k r := by
    intro γ x hγ hx
    have hs' : γᴴ * Hpk k r * γ = Hpk k r := hγ
    have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
    show (γ * x)ᴴ * Hpk k r * (γ * x) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * γᴴ * Hpk k r * (γ * x) = xᴴ * (γᴴ * Hpk k r * γ) * x := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hs', hx']
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  let F : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p =>
    (innerSL ℂ (Φ' (Matrix.of p.2))).smulRight (Φ (Matrix.of p.1 * Matrix.of p.2))
  have hcont : Continuous fun p : Wq × Wp => (innerSL ℂ p.1).smulRight p.2 := by
    have h1 : Continuous fun p : Wq × Wp => innerSL ℂ p.1 := (innerSL ℂ).continuous.comp continuous_fst
    exact ((ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂).comp (h1.prodMk continuous_snd)
  have h1 : ContinuousOn (fun p : Mt k r × Mt k r => Φ' (Matrix.of p.2)) (S ×ˢ S) :=
    hΦ'.comp (hof.comp continuous_snd).continuousOn fun p hp => hp.2
  have h2 : ContinuousOn (fun p : Mt k r × Mt k r => Φ (Matrix.of p.1 * Matrix.of p.2)) (S ×ˢ S) :=
    hΦ.comp ((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).continuousOn
      fun p hp => hmul _ _ hp.1 hp.2
  have hF : ContinuousOn F (S ×ˢ S) := hcont.comp_continuousOn (h1.prodMk h2)
  have hsm : StronglyMeasurable ((S ×ˢ S).indicator F) :=
    stronglyMeasurable_indicator_of_continuousOn (hS.prod hS) hF
  have hint : StronglyMeasurable fun γ => ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG :=
    hsm.integral_prod_right'
  have hm : Measurable fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) :=
    (continuous_hsNormSq.comp_stronglyMeasurable (hint.const_smul (c : ℂ)⁻¹)).measurable
  have hae : ∀ᵐ x ∂μG, x ∈ S := by rw [ae_iff]; exact hH.2.2.1
  have heq : (S.indicator fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) =
      S.indicator fun γ => hsNormSq ((c : ℂ)⁻¹ • ∫ x, (S ×ˢ S).indicator F (γ, x) ∂μG) := by
    refine Set.indicator_congr fun γ hγ => ?_
    unfold ampJ
    congr 2
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    have : (γ, x) ∈ S ×ˢ S := ⟨hγ, hx⟩
    simp only [Set.indicator_of_mem this, F]
  rw [heq]
  exact hm.indicator hS

end GlobalTheory.Amp.AmpMeas
