import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

/- English proof (translation)
Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Establish `h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1` using `congrArg Prod.fst (Units.mul_inv t)`. Rewrite `h` using `[ht.1, one_mul]`. Conclude with `h`. Establish `hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1`.

Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Use `congrArg Valued.v hm` as an intermediate fact. Rewrite `this` using `[map_mul, ht.2 v, one_mul, map_one]`. Then use the resulting hypothesis.
-/
private lemma inv_mem_UU' {t : (A ℚ)ˣ} (ht : t ∈ UU) : t⁻¹ ∈ UU := by
  refine ⟨?_, fun v => ?_⟩
  · have h : (t : A ℚ).1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ).1 = 1 := congrArg Prod.fst (Units.mul_inv t)
    rw [ht.1, one_mul] at h
    exact h
  · have hm : H.cp v (t : A ℚ) * H.cp v ((t⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have := congrArg Valued.v hm
    rwa [map_mul, ht.2 v, one_mul, map_one] at this

/- English proof (translation)
Establish `hi` using `inv_mem_UU' ht`. Establish `fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1` using `fun _ _ => rfl`. Establish `fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1` using `fun _ _ => rfl`. Establish `c00 : (cD t k) 0 0 = k 0 0` using `rfl`. Establish `c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ)` using `rfl`.

Establish `c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0` using `rfl`. Establish `c11 : (cD t k) 1 1 = k 1 1` using `rfl`. Establish `e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Conclude with `congrArg Prod.fst c00`. Use `show ((cD t k) 0 1).1 = (k 0 1).1`. Rewrite using `[c01, fm, hi.1, mul_one]`. Use `show ((cD t k) 1 0).1 = (k 1 0).1`. Rewrite using `[c10, fm, ht.1, one_mul]`.

Conclude with `congrArg Prod.fst c11`. Use `⟨fun i j => ?_, fun v i j => ?_⟩` and prove the remaining obligations. Establish `h` using `hk.1 i j`. Rewrite using `[← h]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]`.

Establish `e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 → (a * b + c * d).1 = (a' * b' + c' * d').1`. Introduce `a b c d a' b' c' d' h1 h2 h3 h4`. Rewrite using `[fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]`. Conclude with `e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)`. Establish `ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ` using `(ht.2 v).le`.

Establish `tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ` using `(hi.2 v).le`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `hk.2 v 0 0`. Use `show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ`. Rewrite using `[c01]`.

Conclude with `mul_mem (hk.2 v 0 1) tj`. Use `show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ`. Rewrite using `[c10]`. Conclude with `mul_mem ti (hk.2 v 1 0)`. Conclude with `hk.2 v 1 1`.
-/
private lemma cD_mem_KK {t : (A ℚ)ˣ} (ht : t ∈ UU) {k : G1 ℚ} (hk : k ∈ KK ℚ) : cD t k ∈ KK ℚ := by
  have hi := inv_mem_UU' ht
  have fm : ∀ a b : A ℚ, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have fa : ∀ a b : A ℚ, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have c00 : (cD t k) 0 0 = k 0 0 := rfl
  have c01 : (cD t k) 0 1 = k 0 1 * ((t⁻¹ : (A ℚ)ˣ) : A ℚ) := rfl
  have c10 : (cD t k) 1 0 = (t : A ℚ) * k 1 0 := rfl
  have c11 : (cD t k) 1 1 = k 1 1 := rfl
  have e1 : ∀ i j, ((cD t k) i j).1 = (k i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg Prod.fst c00
    · show ((cD t k) 0 1).1 = (k 0 1).1
      rw [c01, fm, hi.1, mul_one]
    · show ((cD t k) 1 0).1 = (k 1 0).1
      rw [c10, fm, ht.1, one_mul]
    · exact congrArg Prod.fst c11
  refine ⟨fun i j => ?_, fun v i j => ?_⟩
  · have h := hk.1 i j
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    have e3 : ∀ a b c d a' b' c' d' : A ℚ, a.1 = a'.1 → b.1 = b'.1 → c.1 = c'.1 → d.1 = d'.1 →
        (a * b + c * d).1 = (a' * b' + c' * d').1 := by
      intro a b c d a' b' c' d' h1 h2 h3 h4
      rw [fa, fa, fm, fm, fm, fm, h1, h2, h3, h4]
    exact e3 _ _ _ _ _ _ _ _ (e1 _ _) (e1 _ _) (e1 _ _) (e1 _ _)
  · have ti : ((t : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (ht.2 v).le
    have tj : (((t⁻¹ : (A ℚ)ˣ) : A ℚ)).2 v ∈ v.adicCompletionIntegers ℚ := (hi.2 v).le
    fin_cases i <;> fin_cases j
    · exact hk.2 v 0 0
    · show ((cD t k) 0 1).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c01]
      exact mul_mem (hk.2 v 0 1) tj
    · show ((cD t k) 1 0).2 v ∈ v.adicCompletionIntegers ℚ
      rw [c10]
      exact mul_mem ti (hk.2 v 1 0)
    · exact hk.2 v 1 1

/- English proof (translation)
Introduce `m t ht`. Use `haveI := m.prob`. Establish `hm : Measurable (cD t : G1 ℚ → G1 ℚ)` using `(M.continuous_cD t).measurable`. Establish `hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ`. Rewrite using `[ae_iff]`.

Conclude with `m.supp`. Establish `right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ`. Introduce `f hf k hk`. Use `conv_rhs => rw [← m.κ_right k hk]`. Rewrite using `[lintegral_map hf (measurable_mul_const k)]`.

Establish `left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ`. Introduce `f hf k hk`. Use `conv_rhs => rw [← m.κ_left k hk]`. Rewrite using `[lintegral_map hf (measurable_const_mul k)]`. Use `Measure.ext_of_lintegral _ fun f hf => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_map hf hm]`. Establish `hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2))` using `hf.comp (measurable_fst.mul (hm.comp measurable_snd))`. Establish `hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ`. Establish `h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ` using `hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)`. Rewrite using `[lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]`.

Establish `hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ`. Establish `h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ`. Use `hae.mono fun x hx => ?_` and prove the remaining obligations. Establish `hk : cD t⁻¹ x ∈ KK ℚ` using `cD_mem_KK (inv_mem_UU' ht) hx`. Establish `ex : x = cD t (cD t⁻¹ x)` using `by rw [M.cD_cD, mul_inv_cancel, M.cD_one]`.

Establish `e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y)`. Introduce `y`. Rewrite using `[Function.comp_apply, M.cD_mul, ← ex]`. Simplify using `only [e]`. Conclude with `left (f ∘ cD t) (hf.comp hm) _ hk`.

Rewrite using `[lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]`. Rewrite using `[← hB, ← hA]`. Conclude with `lintegral_lintegral_swap hF.aemeasurable`.
-/
theorem UpperTheory.maximalCompact_measure_map_conjDiag_eq :
    ∀ (M₀ : Meas ℚ) (t : IdeleGroup ℚ), t ∈ UU → M₀.κ.map (cD t) = M₀.κ := by
  intro m t ht
  haveI := m.prob
  have hm : Measurable (cD t : G1 ℚ → G1 ℚ) := (M.continuous_cD t).measurable
  have hae : ∀ᵐ y ∂m.κ, y ∈ KK ℚ := by
    rw [ae_iff]
    exact m.supp
  have right : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (x * k) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_right k hk]
    rw [lintegral_map hf (measurable_mul_const k)]
  have left : ∀ f : G1 ℚ → ℝ≥0∞, Measurable f → ∀ k ∈ KK ℚ, ∫⁻ x, f (k * x) ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    intro f hf k hk
    conv_rhs => rw [← m.κ_left k hk]
    rw [lintegral_map hf (measurable_const_mul k)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hm]
  have hF : Measurable (fun p : G1 ℚ × G1 ℚ => f (p.1 * cD t p.2)) :=
    hf.comp (measurable_fst.mul (hm.comp measurable_snd))
  have hA : ∫⁻ y, ∫⁻ x, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ x, f x ∂m.κ := by
    have h : ∀ᵐ y ∂m.κ, ∫⁻ x, f (x * cD t y) ∂m.κ = ∫⁻ x, f x ∂m.κ :=
      hae.mono fun y hy => right f hf _ (cD_mem_KK ht hy)
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  have hB : ∫⁻ x, ∫⁻ y, f (x * cD t y) ∂m.κ ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
    have h : ∀ᵐ x ∂m.κ, ∫⁻ y, f (x * cD t y) ∂m.κ = ∫⁻ y, f (cD t y) ∂m.κ := by
      refine hae.mono fun x hx => ?_
      have hk : cD t⁻¹ x ∈ KK ℚ := cD_mem_KK (inv_mem_UU' ht) hx
      have ex : x = cD t (cD t⁻¹ x) := by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      have e : ∀ y, f (x * cD t y) = (f ∘ cD t) (cD t⁻¹ x * y) := by
        intro y
        rw [Function.comp_apply, M.cD_mul, ← ex]
      simp only [e]
      exact left (f ∘ cD t) (hf.comp hm) _ hk
    rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]
  rw [← hB, ← hA]
  exact lintegral_lintegral_swap hF.aemeasurable
