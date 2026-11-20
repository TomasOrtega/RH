import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

/- English proof (translation)
Use `set c := ∫ s in (0:ℝ)..1, h s with hcdef`. Establish `hnn : 0 ≤ ∫ s in (0:ℝ)..1, (h s - c) ^ 2` using `intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)`. Establish `hexp : ∫ s in (0:ℝ)..1, (h s - c) ^ 2 = (∫ s in (0:ℝ)..1, h s ^ 2) - 2 * c * c + c ^ 2`. Establish `e1 : (fun s => (h s - c) ^ 2) = fun s => (h s ^ 2 - (2 * c) * h s) + c ^ 2`. Use function extensionality and compare the values at `s`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]`. Simplify using the standard rewrite rules. Conclude with `Or.inl rfl`. Conclude with `(hc.pow 2).intervalIntegrable _ _`.

Conclude with `(continuous_const.mul hc).intervalIntegrable _ _`. Conclude with `((hc.pow 2).sub (continuous_const.mul hc)).intervalIntegrable _ _`. Conclude with `continuous_const.intervalIntegrable _ _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sq_intervalIntegral_unit_le (h : ℝ → ℝ) (hc : Continuous h) :
    (∫ s in (0:ℝ)..1, h s) ^ 2 ≤ ∫ s in (0:ℝ)..1, h s ^ 2 := by
  set c := ∫ s in (0:ℝ)..1, h s with hcdef
  have hnn : 0 ≤ ∫ s in (0:ℝ)..1, (h s - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have hexp : ∫ s in (0:ℝ)..1, (h s - c) ^ 2 = (∫ s in (0:ℝ)..1, h s ^ 2) - 2 * c * c + c ^ 2 := by
    have e1 : (fun s => (h s - c) ^ 2) = fun s => (h s ^ 2 - (2 * c) * h s) + c ^ 2 := by
      funext s; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp
      exact Or.inl rfl
    · exact (hc.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hc).intervalIntegrable _ _
    · exact ((hc.pow 2).sub (continuous_const.mul hc)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  nlinarith

/- English proof (translation)
Introduce `n ε d φ hφ Y hY`. Take `⟨hRmem, hRder⟩` from `rder_mem_and_hasDerivAt ε d φ hφ Y hY`. Use `set R := rder ε [Y] φ with hRdef`. Establish `hRc : Continuous R` using `continuous_of_mem hRmem`. Establish `hφc : Continuous φ` using `continuous_of_mem hφ`.

Use `haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩`. Use `haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1`. Establish `hEG` using `group_exponential_facts n ε Y hY.1`. Establish `hEK` using `hEG.2.2.2 hY`. Set `e : ℝ → KG ε` to `fun t => expK ε Y t`.

Establish `he_add : ∀ s t, e (s + t) = e s * e t` using `fun s t => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((expK ε Y (s + t) : KG ε) : UJ ε) = (expK ε Y s : UJ ε) * (expK ε Y t : UJ ε)`. Rewrite using `[hEK.1, hEK.1, hEK.1]`. Conclude with `hEG.2.1 s t`.

Establish `he0 : e 0 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((expK ε Y 0 : KG ε) : UJ ε) = 1`. Rewrite using `[hEK.1]`. Conclude with `hEG.1`.

Establish `he_cont : Continuous e` using `hEK.2`. Establish `hder' : ∀ k s, HasDerivAt (fun t => φ (k * e t)) (R (k * e s)) s`. Introduce `k s`. Establish `h1` using `hRder (k * e s)`. Establish `h2 : HasDerivAt (fun t => φ (k * e s * expK ε Y (t - s))) (R (k * e s)) s` using `HasDerivAt.comp_sub_const (f := fun t => φ (k * e s * expK ε Y t)) s s (by rw [sub_self]; exact h1)`.

Establish `hfun : (fun t => φ (k * e s * expK ε Y (t - s))) = fun t => φ (k * e t)`. Use function extensionality and compare the values at `t`. Use `show φ (k * e s * e (t - s)) = φ (k * e t)`. Rewrite using `[mul_assoc, ← he_add, add_sub_cancel]`. Rewrite `h2` using `[hfun]`.

Conclude with `h2`. Establish `hgc : ∀ k, Continuous (fun s => R (k * e s))` using `fun k => hRc.comp (continuous_const.mul he_cont)`. Establish `hftc : ∀ k, ∫ s in (0:ℝ)..1, R (k * e s) = φ (k * e 1) - φ k`. Introduce `k`. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder' k s) ((hgc k).intervalIntegrable 0 1), he0, mul_one]`.

Establish `hpt : ∀ k, ‖φ k - φ (k * e 1)‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ ^ 2`. Introduce `k`. Establish `h1 : ‖φ k - φ (k * e 1)‖ ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖`. Rewrite using `[norm_sub_rev, ← hftc k]`. Conclude with `intervalIntegral.norm_integral_le_integral_norm zero_le_one`.

Establish `h2` using `sq_intervalIntegral_unit_le (fun s => ‖R (k * e s)‖) ((hgc k).norm)`. Combine the equalities or inequalities in the displayed calculation. Establish `hRsc : Continuous (fun x => ‖R x‖ ^ 2)` using `hRc.norm.pow 2`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hRsc.continuousOn`. Establish `hcont2 : Continuous (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2)` using `hRsc.comp (continuous_fst.mul (he_cont.comp continuous_snd))`.

Establish `hI : Integrable (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2) ((muK ε).prod (volume.restrict (Set.Ioc (0:ℝ) 1)))` using `by haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by`. Rewrite using `[isFiniteMeasure_restrict]`. Simplify using the standard rewrite rules. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))`. Establish `hemb : Topology.IsEmbedding (fun k : KG ε => toMK k)` using `(isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal`.

Use `haveI : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology`. Use `haveI : SecondCountableTopology (KG ε × ℝ) := inferInstance`. Conclude with `Integrable.of_bound hcont2.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hC _ (Set.mem_univ _))`. Establish `hswap` using `integral_integral_swap hI`. Establish `hrhs : ∫ x, (∫ s in (0:ℝ)..1, ‖R (x * e s)‖ ^ 2) ∂(muK ε) = ∫ x, ‖R x‖ ^ 2 ∂(muK ε)`.

Simplify using `only [intervalIntegral.integral_of_le zero_le_one]`. Rewrite using `[hswap]`. Repeatedly rewrite using `[integral_mul_right_eq_self (μ := muK ε) (fun x => ‖R x‖ ^ 2)]`. Rewrite using `[setIntegral_const]`. Simplify using the standard rewrite rules.

Rewrite using `[← hrhs]`. Apply `integral_mono_of_nonneg` to reduce the goal to its premises. Conclude with `Filter.Eventually.of_forall fun x => by positivity`. Use `hI.integral_prod_left` as an intermediate fact. Simplify using `only [Function.uncurry_apply_pair] at this`.

Use `this.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [intervalIntegral.integral_of_le zero_le_one]`. Conclude with `Filter.Eventually.of_forall fun x => hpt x`.
-/
theorem norm_sub_expK_sq_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  intro n ε d φ hφ Y hY
  obtain ⟨hRmem, hRder⟩ := rder_mem_and_hasDerivAt ε d φ hφ Y hY
  set R := rder ε [Y] φ with hRdef
  have hRc : Continuous R := continuous_of_mem hRmem
  have hφc : Continuous φ := continuous_of_mem hφ
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hEG := group_exponential_facts n ε Y hY.1
  have hEK := hEG.2.2.2 hY
  let e : ℝ → KG ε := fun t => expK ε Y t
  have he_add : ∀ s t, e (s + t) = e s * e t := fun s t => by
    apply Subtype.ext
    show ((expK ε Y (s + t) : KG ε) : UJ ε) = (expK ε Y s : UJ ε) * (expK ε Y t : UJ ε)
    rw [hEK.1, hEK.1, hEK.1]
    exact hEG.2.1 s t
  have he0 : e 0 = 1 := by
    apply Subtype.ext
    show ((expK ε Y 0 : KG ε) : UJ ε) = 1
    rw [hEK.1]; exact hEG.1
  have he_cont : Continuous e := hEK.2
  have hder' : ∀ k s, HasDerivAt (fun t => φ (k * e t)) (R (k * e s)) s := by
    intro k s
    have h1 := hRder (k * e s)
    have h2 : HasDerivAt (fun t => φ (k * e s * expK ε Y (t - s))) (R (k * e s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => φ (k * e s * expK ε Y t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => φ (k * e s * expK ε Y (t - s))) = fun t => φ (k * e t) := by
      funext t
      show φ (k * e s * e (t - s)) = φ (k * e t)
      rw [mul_assoc, ← he_add, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have hgc : ∀ k, Continuous (fun s => R (k * e s)) := fun k =>
    hRc.comp (continuous_const.mul he_cont)
  have hftc : ∀ k, ∫ s in (0:ℝ)..1, R (k * e s) = φ (k * e 1) - φ k := by
    intro k
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder' k s)
      ((hgc k).intervalIntegrable 0 1), he0, mul_one]
  have hpt : ∀ k, ‖φ k - φ (k * e 1)‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ ^ 2 := by
    intro k
    have h1 : ‖φ k - φ (k * e 1)‖ ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ := by
      rw [norm_sub_rev, ← hftc k]
      exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    have h2 := sq_intervalIntegral_unit_le (fun s => ‖R (k * e s)‖) ((hgc k).norm)
    calc ‖φ k - φ (k * e 1)‖ ^ 2 ≤ (∫ s in (0:ℝ)..1, ‖R (k * e s)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hRsc : Continuous (fun x => ‖R x‖ ^ 2) := hRc.norm.pow 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hRsc.continuousOn
  have hcont2 : Continuous (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2) :=
    hRsc.comp (continuous_fst.mul (he_cont.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2)
      ((muK ε).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [isFiniteMeasure_restrict]; simp
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    haveI : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (KG ε × ℝ) := inferInstance
    exact Integrable.of_bound hcont2.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _ (Set.mem_univ _))
  have hswap := integral_integral_swap hI
  have hrhs : ∫ x, (∫ s in (0:ℝ)..1, ‖R (x * e s)‖ ^ 2) ∂(muK ε) = ∫ x, ‖R x‖ ^ 2 ∂(muK ε) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    rw [hswap]
    simp_rw [integral_mul_right_eq_self (μ := muK ε) (fun x => ‖R x‖ ^ 2)]
    rw [setIntegral_const]
    simp
  rw [← hrhs]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => by positivity
  · have := hI.integral_prod_left
    simp only [Function.uncurry_apply_pair] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [intervalIntegral.integral_of_le zero_le_one]
  · exact Filter.Eventually.of_forall fun x => hpt x

end GlobalTheory.KFourier

end
