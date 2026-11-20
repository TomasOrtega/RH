import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal FourierTransform ContDiff RealInnerProductSpace

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_bump_fourier : ∃ φ : ℝ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ φ 0 = 1 ∧
    Integrable (fun s : ℝ => ∫ u : ℝ, φ u * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (s : ℂ)))) ∧
    ∫ s : ℝ, (∫ u : ℝ, φ u * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (s : ℂ)))) = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hsm : ContDiff ℝ ∞ (fun u : ℝ => ((b u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hcs : HasCompactSupport (fun u : ℝ => ((b u : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let ψ : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hsm
  have hψ : ∀ u, ψ u = ((b u : ℝ) : ℂ) := fun u => rfl
  have key : ∀ s : ℝ, (∫ u : ℝ, ((b u : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (s : ℂ))))
      = (𝓕⁻ ψ) s := by
    intro s
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul, hψ]
    rw [mul_comm]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  refine ⟨fun u => ((b u : ℝ) : ℂ), hsm.continuous, hcs, by simp [hb0], ?_, ?_⟩
  · simp only [key]
    exact (𝓕⁻ ψ).integrable
  · simp only [key]
    have e : 𝓕 (𝓕⁻ ψ) = ψ := FourierInvPair.fourier_fourierInv_eq ψ
    have e0 := congrArg (fun g : SchwartzMap ℝ ℂ => g 0) e
    rw [SchwartzMap.fourier_coe, Real.fourier_eq] at e0
    simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul] at e0
    rw [e0, hψ, hb0]
    simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem integral_prod3 {ι : Type} [Fintype ι] {n : ℕ} (f : ι → Fin n → Fin n → ℝ → ℂ) :
    ∫ u : ι → WR.E n, ∏ i, ∏ a, ∏ b, f i a b (u i a b) = ∏ i, ∏ a, ∏ b, ∫ t : ℝ, f i a b t := by
  rw [integral_fintype_prod_volume_eq_prod (fun i (v : WR.E n) => ∏ a, ∏ b, f i a b (v a b))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℝ) => ∏ b, f i a b (r b))]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact integral_fintype_prod_volume_eq_prod (fun b (t : ℝ) => f i a b t)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem integrable_prod3 {ι : Type} [Fintype ι] {n : ℕ} (f : ι → Fin n → Fin n → ℝ → ℂ)
    (hf : ∀ i a b, Integrable (f i a b)) :
    Integrable (fun u : ι → WR.E n => ∏ i, ∏ a, ∏ b, f i a b (u i a b)) := by
  have h : ∀ i, Integrable (fun v : WR.E n => ∏ a, ∏ b, f i a b (v a b)) := by
    intro i
    have h2 : ∀ a, Integrable (fun w : Fin n → ℝ => ∏ b, f i a b (w b)) := fun a =>
      Integrable.fintype_prod (f := fun b t => f i a b t) (μ := fun _ => volume) (fun b => hf i a b)
    exact Integrable.fintype_prod (f := fun a (w : Fin n → ℝ) => ∏ b, f i a b (w b))
      (μ := fun _ => volume) h2
  exact Integrable.fintype_prod (f := fun i (v : WR.E n) => ∏ a, ∏ b, f i a b (v a b))
    (μ := fun _ => volume) h

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_pair3 {ι : Type} [Fintype ι] {n : ℕ} (l : ι → ℝ) (u w : ι → WR.E n) :
    Complex.exp (2 * Real.pi * Complex.I * ∑ i, (l i : ℂ) * ∑ a, ∑ b, ((u i a b : ℝ) : ℂ) * ((w i a b : ℝ) : ℂ)) =
      ∏ i, ∏ a, ∏ b, Complex.exp (2 * Real.pi * Complex.I * (((u i a b : ℝ) : ℂ) * ((l i * w i a b : ℝ) : ℂ))) := by
  simp_rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  congr 1
  push_cast
  ring

set_option maxHeartbeats 400000 in

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem selfDual_const {H : Type} [AddCommGroup H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    {ι : Type} [Fintype ι] {n : ℕ} (l : ι → ℝ) (hl : ∀ i, l i ≠ 0)
    (ν : Measure H) (χ : H → H → ℂ) (hsd : SelfDual ν χ)
    (eb eg : H ≃ₜ (ι → WR.E n)) (heb0 : eb 0 = 0)
    (hχ : ∀ x y, χ x y = Complex.exp (2 * Real.pi * Complex.I *
      ∑ i, (l i : ℂ) * ∑ a, ∑ b, ((eb x i a b : ℝ) : ℂ) * ((eg y i a b : ℝ) : ℂ)))
    (hsym : ∀ x y, χ x y = χ y x)
    (cb cg : ℝ≥0) (hb : ν.map eb = cb • volume) (hg : ν.map eg = cg • volume) :
    ((cb : ℝ) * cg) = ∏ i, |l i| ^ (n ^ 2) := by
  obtain ⟨φ, hφc, hφs, hφ0, hFi, hF1⟩ := exists_bump_fourier
  let F : ℝ → ℂ := fun s => ∫ u : ℝ, φ u * Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * (s : ℂ)))
  have hFi' : Integrable F := hFi
  have hF1' : ∫ s, F s = 1 := hF1
  let P : (ι → WR.E n) → ℂ := fun v => ∏ i, ∏ a, ∏ b, φ (v i a b)
  have hPc : Continuous P := by
    refine continuous_finset_prod _ fun i _ => continuous_finset_prod _ fun a _ =>
      continuous_finset_prod _ fun b _ => ?_
    exact hφc.comp ((continuous_apply b).comp ((continuous_apply a).comp (continuous_apply i)))
  have hPs : HasCompactSupport P := by
    refine HasCompactSupport.intro (K := Set.univ.pi fun _ : ι => Set.univ.pi fun _ : Fin n =>
      Set.univ.pi fun _ : Fin n => tsupport φ) ?_ ?_
    · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hφs.isCompact
    · intro v hv
      simp only [Set.mem_univ_pi, not_forall] at hv
      obtain ⟨i, a, b, h⟩ := hv
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ a)
        (Finset.prod_eq_zero (Finset.mem_univ b) (image_eq_zero_of_notMem_tsupport h)))
  have hinner : ∀ y, ∫ x, P (eb x) * χ x y ∂ν
      = ((cb : ℝ) : ℂ) * ∏ i, ∏ a, ∏ b, F (l i * eg y i a b) := by
    intro y
    let Q : (ι → WR.E n) → ℂ := fun v => ∏ i, ∏ a, ∏ b, (φ (v i a b) *
      Complex.exp (2 * Real.pi * Complex.I * (((v i a b : ℝ) : ℂ) * ((l i * eg y i a b : ℝ) : ℂ))))
    have h1 : ∀ x, P (eb x) * χ x y = Q (eb x) := by
      intro x
      simp only [P, Q, hχ, exp_pair3, ← Finset.prod_mul_distrib]
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), ← eb.measurableEmbedding.integral_map Q, hb,
      integral_smul_nnreal_measure,
      integral_prod3 (fun i a b t => φ t * Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * ((l i * eg y i a b : ℝ) : ℂ)))),
      NNReal.smul_def, Complex.real_smul]
  have hint : Integrable (fun y => ∫ x, P (eb x) * χ x y ∂ν) ν := by
    rw [show (fun y => ∫ x, P (eb x) * χ x y ∂ν)
      = fun y => ((cb : ℝ) : ℂ) * ∏ i, ∏ a, ∏ b, F (l i * eg y i a b) from funext hinner]
    have hG : Integrable (fun w : ι → WR.E n => ((cb : ℝ) : ℂ) * ∏ i, ∏ a, ∏ b, F (l i * w i a b)) := by
      refine Integrable.const_mul ?_ _
      exact integrable_prod3 (fun i a b t => F (l i * t)) (fun i a b => hFi'.comp_mul_left' (hl i))
    have hG' := hG.smul_measure_nnreal (c := cg)
    rw [← hg, eg.measurableEmbedding.integrable_map_iff] at hG'
    exact hG'
  have hsd2 := hsd.2 (fun x => P (eb x)) (hPc.comp eb.continuous) (hPs.comp_homeomorph eb) hint 0
  have hχ0 : ∀ y, χ y 0 = 1 := by
    intro y
    rw [hsym, hχ, heb0]
    simp
  have hP0 : P 0 = 1 := by simp [P, hφ0]
  simp only [hχ0, mul_one, neg_zero, heb0, hinner, hP0] at hsd2
  rw [integral_const_mul, ← eg.measurableEmbedding.integral_map
      (fun w : ι → WR.E n => ∏ i, ∏ a, ∏ b, F (l i * w i a b)), hg, integral_smul_nnreal_measure,
    integral_prod3 (fun i a b t => F (l i * t)), NNReal.smul_def, Complex.real_smul] at hsd2
  simp only [Measure.integral_comp_mul_left (fun t => F t), hF1', Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Complex.real_smul, mul_one] at hsd2
  have hA : (∏ i, |l i| ^ (n ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (abs_ne_zero.mpr (hl i))
  have hX : (∏ i, (((|(l i)⁻¹| : ℝ) : ℂ) ^ n) ^ n) = (((∏ i, |l i| ^ (n ^ 2) : ℝ)) : ℂ)⁻¹ := by
    push_cast
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [abs_inv, Complex.ofReal_inv, ← pow_mul, ← sq, inv_pow]
  rw [hX] at hsd2
  have hA' : ((∏ i, |l i| ^ (n ^ 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  field_simp at hsd2
  exact_mod_cast hsd2

end PositivityTheory.SiegelWeilFormula.GReal
