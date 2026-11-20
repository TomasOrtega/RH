import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroupStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoffStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotWeil

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Use `Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_` and prove the remaining obligations. Conclude with `(measurable_pi_apply k).comp ((measurable_pi_apply i).comp ha)`. Conclude with `(measurable_pi_apply j).comp ((measurable_pi_apply k).comp hb)`.
-/
theorem measurable_mulM {m : ℕ} {α : Type} [MeasurableSpace α] {a b : α → PI.MtM m}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun t => (fun i j => (Matrix.of (a t) * Matrix.of (b t)) i j : PI.MtM m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp ha)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hb)

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `hc : Continuous (fun s : PI.MtM m => (Matrix.of s : Matrix (Fin m) (Fin m) ℂ))` using `continuous_id`. Simplify using `only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]`. Use `Measurable.mul (Measurable.inv hc.matrix_det.measurable) ?_` and prove the remaining obligations. Conclude with `(hc.matrix_adjugate.matrix_elem i j).measurable`.
-/
theorem measurable_invM {m : ℕ} :
    Measurable (fun s : PI.MtM m => (fun i j => (Matrix.of s)⁻¹ i j : PI.MtM m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hc : Continuous (fun s : PI.MtM m => (Matrix.of s : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  refine Measurable.mul (Measurable.inv hc.matrix_det.measurable) ?_
  exact (hc.matrix_adjugate.matrix_elem i j).measurable

/- English proof (translation)
Establish `hl : ∀ s, Measurable (mu s)` using `fun s => hmu.comp (measurable_const.prodMk measurable_id)`. Establish `hr : ∀ x, Measurable (fun s => mu s x)` using `fun x => hmu.comp (measurable_id.prodMk measurable_const)`. Establish `h1 : Measurable (fun p : X × X => f (mu p.2 p.1))` using `hf.comp (hmu.comp measurable_swap)`. Establish `h2 : Measurable (fun p : X × X => φ (mu (iv p.1) p.2) * f p.2)` using `(hφ.comp (hmu.comp ((hiv.comp measurable_fst).prodMk measurable_snd))).mul (hf.comp measurable_snd)`. Establish `hF : Measurable (fun x : X => ∫⁻ s, f (mu s x) ∂μS)` using `h1.lintegral_prod_right'`.

Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hφ hF]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[Pi.mul_apply, lintegral_const_mul]`.

Conclude with `hf.comp (hr x)`. Use `_ = ∫⁻ s, ∫⁻ x, φ x * f (mu s x) ∂μG ∂μS := lintegral_lintegral_swap ((hφ.comp measurable_fst).mul h1).aemeasurable`. Use `_ = ∫⁻ s, ∫⁻ y, φ (mu (iv s) y) * f y ∂μG ∂μS := by`. Use `lintegral_congr_ae (hleft.mono fun s hs => ?_)` and prove the remaining obligations. Establish `hm : Measurable (fun y : X => φ (mu (iv s) y) * f y)` using `(hφ.comp (hl _)).mul hf`.

Use `beta_reduce`. Use `conv_rhs => rw [← hs.1, lintegral_map hm (hl s)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[hs.2]`. Use `_ = ∫⁻ y, ∫⁻ s, φ (mu (iv s) y) * f y ∂μS ∂μG := lintegral_lintegral_swap h2.aemeasurable`.

Use `_ = ∫⁻ y, f y ∂μG := by`. Use `lintegral_congr_ae (hφ1.mono fun y hy => ?_)` and prove the remaining obligations. Establish `hm : Measurable (fun s : X => φ (mu s y))` using `hφ.comp (hr y)`. Establish `hm' : Measurable (fun s : X => φ (mu (iv s) y))` using `hm.comp hiv`. Use `hinv _ hm` as an intermediate fact.

Use `beta_reduce at this ⊢`. Rewrite using `[lintegral_mul_const _ hm', this, hy, one_mul]`.
-/
theorem unfold_abstract {X : Type} [MeasurableSpace X] (mu : X → X → X) (iv : X → X)
    (hmu : Measurable (fun p : X × X => mu p.1 p.2)) (hiv : Measurable iv)
    (μG μS : Measure X) [SFinite μG] [SFinite μS]
    (hleft : ∀ᵐ s ∂μS, μG.map (mu s) = μG ∧ ∀ x, mu (iv s) (mu s x) = x)
    (hinv : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ s, f (iv s) ∂μS = ∫⁻ s, f s ∂μS)
    (φ : X → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∀ᵐ x ∂μG, ∫⁻ s, φ (mu s x) ∂μS = 1)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (mu s x) ∂μS) ∂(μG.withDensity φ) := by
  have hl : ∀ s, Measurable (mu s) := fun s => hmu.comp (measurable_const.prodMk measurable_id)
  have hr : ∀ x, Measurable (fun s => mu s x) := fun x =>
    hmu.comp (measurable_id.prodMk measurable_const)
  have h1 : Measurable (fun p : X × X => f (mu p.2 p.1)) := hf.comp (hmu.comp measurable_swap)
  have h2 : Measurable (fun p : X × X => φ (mu (iv p.1) p.2) * f p.2) :=
    (hφ.comp (hmu.comp ((hiv.comp measurable_fst).prodMk measurable_snd))).mul
      (hf.comp measurable_snd)
  have hF : Measurable (fun x : X => ∫⁻ s, f (mu s x) ∂μS) := h1.lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hF]
  symm
  calc ∫⁻ x, (φ * fun x : X => ∫⁻ s, f (mu s x) ∂μS) x ∂μG
      = ∫⁻ x, ∫⁻ s, φ x * f (mu s x) ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, lintegral_const_mul]
        exact hf.comp (hr x)
    _ = ∫⁻ s, ∫⁻ x, φ x * f (mu s x) ∂μG ∂μS :=
        lintegral_lintegral_swap ((hφ.comp measurable_fst).mul h1).aemeasurable
    _ = ∫⁻ s, ∫⁻ y, φ (mu (iv s) y) * f y ∂μG ∂μS := by
        refine lintegral_congr_ae (hleft.mono fun s hs => ?_)
        have hm : Measurable (fun y : X => φ (mu (iv s) y) * f y) :=
          (hφ.comp (hl _)).mul hf
        beta_reduce
        conv_rhs => rw [← hs.1, lintegral_map hm (hl s)]
        refine lintegral_congr fun x => ?_
        rw [hs.2]
    _ = ∫⁻ y, ∫⁻ s, φ (mu (iv s) y) * f y ∂μS ∂μG := lintegral_lintegral_swap h2.aemeasurable
    _ = ∫⁻ y, f y ∂μG := by
        refine lintegral_congr_ae (hφ1.mono fun y hy => ?_)
        have hm : Measurable (fun s : X => φ (mu s y)) := hφ.comp (hr y)
        have hm' : Measurable (fun s : X => φ (mu (iv s) y)) := hm.comp hiv
        have := hinv _ hm
        beta_reduce at this ⊢
        rw [lintegral_mul_const _ hm', this, hy, one_mul]

/- English proof (translation)
Introduce `m G S μG μS hG hS hSG hμG hμS hR`. Take `⟨φ, hφ, hφ1⟩` from `GlobalTheory.T.exists_normalised_cutoff' m G S μS hG hS hSG hμS hR`. Establish `hinv` using `GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup m S μS hS hμS hR`. Use `haveI := hμG.1`. Use `haveI := hμS.1`.

Establish `haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ S` using `by rw [ae_iff]; exact hμS.2.2.1`. Establish `haeG : ∀ᵐ s ∂μG, Matrix.of s ∈ G` using `by rw [ae_iff]; exact hμG.2.2.1`. Use `⟨μG.withDensity φ, fun f hf => ?_⟩` and prove the remaining obligations. Use `unfold_abstract (fun s x : PI.MtM m => fun i j => (Matrix.of s * Matrix.of x) i j) (fun s i j => (Matrix.of s)⁻¹ i j) (measurable_mulM measurable_fst measurable_snd) measurable_invM μG μS (haeS.mono fun s hs => ⟨hμG.2.2.2 _ (hSG hs), fun x => ?_⟩) hinv φ hφ (haeG.mono fun x hx => …` and prove the remaining obligations. Establish `hs1 : (Matrix.of s)⁻¹ * Matrix.of s = 1` using `mul_eq_one_comm.1 (hS.2.2.2 _ hs).2`.

Express the relevant statement in the definitionally equal form `(Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x`. Rewrite using `[← Matrix.mul_assoc, hs1, Matrix.one_mul]`.
-/
theorem exists_isQuotM : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS : Measure (PI.MtM m)),
    PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM G μG → PI.IsHaarOnM S μS →
    PI.IsRightInvM S μS → ∃ ν, PI.IsQuotM μG μS ν := by
  intro m G S μG μS hG hS hSG hμG hμS hR
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS hG hS hSG hμS hR
  have hinv := GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup m S μS hS hμS hR
  haveI := hμG.1
  haveI := hμS.1
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ S := by rw [ae_iff]; exact hμS.2.2.1
  have haeG : ∀ᵐ s ∂μG, Matrix.of s ∈ G := by rw [ae_iff]; exact hμG.2.2.1
  refine ⟨μG.withDensity φ, fun f hf => ?_⟩
  refine unfold_abstract (fun s x : PI.MtM m => fun i j => (Matrix.of s * Matrix.of x) i j)
    (fun s i j => (Matrix.of s)⁻¹ i j) (measurable_mulM measurable_fst measurable_snd)
    measurable_invM μG μS (haeS.mono fun s hs => ⟨hμG.2.2.2 _ (hSG hs), fun x => ?_⟩) hinv φ hφ
    (haeG.mono fun x hx => hφ1 x hx) f hf
  have hs1 : (Matrix.of s)⁻¹ * Matrix.of s = 1 := mul_eq_one_comm.1 (hS.2.2.2 _ hs).2
  change (Matrix.of s)⁻¹ * (Matrix.of s * Matrix.of x) = Matrix.of x
  rw [← Matrix.mul_assoc, hs1, Matrix.one_mul]

end GlobalTheory.QuotWeil
