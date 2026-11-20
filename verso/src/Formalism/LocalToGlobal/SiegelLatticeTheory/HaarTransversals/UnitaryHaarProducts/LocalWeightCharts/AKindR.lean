import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationContinuous

noncomputable section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace WlocSk.AK

open WlocSk WlocSk.PtD Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.WuDecay Formalism.L2.SG.SplitPrimeNormLemmas

variable {k r : ℕ}

section Kernel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
  {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Vp →L[ℂ] Vp)}

def bLin (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (σ : Mat k r → (H →L[ℂ] H))
    (π : Mat k r → (Vp →L[ℂ] Vp)) (w' : H) (ξ : Vp) (p : Mt k r × Mt k r) : H →L[ℂ] Vp :=
  star (psiGen k r z c (Matrix.of p.2)) •
    ((innerSL ℂ w').comp (σ (Matrix.of p.1 * Matrix.of p.2))).smulRight (π (Matrix.of p.1)⁻¹ ξ)

/- English proof (translation)
Simplify using `only [bLin, bInt, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_smul]`. Rewrite using `[mul_comm]`.
-/
theorem bLin_apply (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (w' : H) (ξ : Vp)
    (p : Mt k r × Mt k r) (v : H) : bLin z c σ π w' ξ p v = bInt z c σ π w' ξ v p := by
  simp only [bLin, bInt, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_smul]
  rw [mul_comm]

/- English proof (translation)
Use `set F : Mt k r × (Mt k r × Mt k r) → Vp := fun q => β (Matrix.of q.1) • bInt z c σ π w' ξ (σ (x * Matrix.of q.1) w) q.2 with hFdef`. Establish `hG : ∀ᵐ g ∂μG, Matrix.of g ∈ Gr k r` using `ae_gr hGc`. Establish `hq1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Gr k r` using `Measure.quasiMeasurePreserving_fst.ae hG`. Establish `hq2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.1 * Matrix.of q.2.2 ∈ Gr k r` using `Measure.quasiMeasurePreserving_snd.ae hae`. Use `set T : Set (Mt k r × (Mt k r × Mt k r)) := {q | Matrix.of q.1 ∈ Gr k r ∧ Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.1 * Matrix.of q.2.2 ∈ Gr k r} with hTdef`.

Establish `hc1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mat k r)` using `continuous_fst`. Establish `hc21 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mat k r)` using `continuous_fst.comp continuous_snd`. Establish `hc22 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mat k r)` using `continuous_snd.comp continuous_snd`. Establish `hcm : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 * Matrix.of q.2.2 : Mat k r)` using `hc21.matrix_mul hc22`. Establish `hcy : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1) : Mat k r)` using `hcm.matrix_mul (continuous_const.matrix_mul hc1)`.

Establish `hTc : IsClosed T` using `(gr_isClosed.preimage hc1).inter ((hUWc.preimage hc21).inter (gr_isClosed.preimage hcm))`. Establish `hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ T` using `by filter_upwards [hq1, hq2] with q h1 h2`. Conclude with `⟨h1, h2⟩`. Use `set F' : Mt k r × (Mt k r × Mt k r) → Vp := fun q => (⟪w', σ (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1)) w⟫_ℂ * star (psiGen k r z c (Matrix.of q.2.2))) • π (Matrix.of q.2.1)⁻¹ ξ with hF'def`. Establish `hF'c : ContinuousOn F' T`.

Establish `h1 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => σ (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1)) w) T` using `(hσ.2.2 w).comp hcy.continuousOn (fun q hq => gr_mul hq.2.2 (gr_mul hx hq.1))`. Establish `hi : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1)⁻¹) T` using `inv_contOn.comp hc21.continuousOn (fun q hq => hUWG hq.2.1)`. Establish `h2 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => π (Matrix.of q.2.1)⁻¹ ξ) T` using `(hπc ξ).comp hi (fun q hq => hUWinv _ hq.2.1)`. Establish `h3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => star (psiGen k r z c (Matrix.of q.2.2))` using `continuous_star.comp ((psiGen_cont z c).comp hc22)`. Conclude with `((continuousOn_const.inner h1).mul h3.continuousOn).smul h2`.

Establish `hF'm : AEStronglyMeasurable F' (μG.prod (μW.prod μN))`. Use `hF'c.aestronglyMeasurable (μ := μG.prod (μW.prod μN)) hTc.measurableSet` as an intermediate fact. Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem hTae]`. Then use the resulting hypothesis. Establish `hFm : AEStronglyMeasurable F (μG.prod (μW.prod μN))`. Use `((hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).smul hF'm).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hTae] with q hq`. Use `show β (Matrix.of q.1) • F' q = β (Matrix.of q.1) • bInt z c σ π w' ξ (σ (x * Matrix.of q.1) w) q.2`. Use `congr 1`. Simplify using `only [hF'def, bInt]`. Rewrite using `[← sigma_mul hσ hq.2.2 (gr_mul hx hq.1)]`.

Establish `hlin : ∫⁻ q, ‖F q‖ₑ ∂(μG.prod (μW.prod μN)) < ⊤`. Rewrite using `[lintegral_prod _ hFm.enorm]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Simplify using `only [hFdef, enorm_smul]`.

Conclude with `lintegral_const_mul' _ _ enorm_ne_top`. Use `_ ≤ ∫⁻ g, ENNReal.ofReal (C * opn x ^ N1H k r) * (‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) ∂μG := by`. Apply `lintegral_mono_ae` to reduce the goal to its premises. Use `filter_upwards [hG] with g hg`. Establish `hb` using `hB _ (gr_mul hx hg)`.

Establish `hN` using `nilradical_half_sum_nonneg (k := k) (r := r)`. Establish `h1 : C * opn (x * Matrix.of g) ^ N1H k r ≤ C * opn x ^ N1H k r * opn (Matrix.of g) ^ N1H k r`. Rewrite using `[mul_assoc, ← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]`. Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (opn_nonneg _) (opn_mul _ _) hN) hC`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hb.trans (ENNReal.ofReal_le_ofReal h1)`. Use `_ = _ := by`. Rewrite using `[ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg (opn_nonneg _) _))]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ENNReal.ofReal (C * opn x ^ N1H k r) * ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.

Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hβw`. Establish `hint : Integrable F (μG.prod (μW.prod μN))` using `⟨hFm, hlin⟩`. Establish `hsl : ∀ g : Mt k r, ∫ p, F (g, p) ∂(μW.prod μN) = β (Matrix.of g) • B0 z c σ π μW μN w' ξ (σ (x * Matrix.of g) w)` using `fun g => by`. Simplify using `only [hFdef, B0]`. Conclude with `integral_smul _ _`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `hint.integral_prod_left` as an intermediate fact. Simplify using `only [hsl] at this`. Conclude with `this`. Establish `hsw` using `integral_integral_swap (f := fun g p => F (g, p)) hint`.

Simplify using `only [hsl] at hsw`. Rewrite using `[hsw]`. Simplify using `only [B0]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `show ∫ g, F (g, p) ∂μG = bInt z c σ π w' ξ (σ x w) p`.

Establish `hcomp : ∀ᵐ g ∂μG, F (g, p) = ((bLin z c σ π w' ξ p).comp (σ x)) (β (Matrix.of g) • σ (Matrix.of g) w)` using `by filter_upwards [hG] with g hg`. Simplify using `only [hFdef, ContinuousLinearMap.comp_apply, map_smul, bLin_apply]`. Rewrite using `[sigma_mul hσ hx hg]`. Rewrite using `[integral_congr_ae hcomp, ContinuousLinearMap.integral_comp_comm _ hβi, hβr, ContinuousLinearMap.comp_apply, bLin_apply]`.
-/
theorem integrable_and_integral_smul_B0_eq (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (hσ : IsURepOn (Gr k r) σ)
    {μG μW μN : Measure (Mt k r)} [SFinite μG] [SFinite μW] [SFinite μN]
    (hGc : μG {x | Matrix.of x ∉ Gr k r} = 0)
    (hUWc : IsClosed (UWset k r z)) (hUWG : UWset k r z ⊆ Gr k r)
    (hUWinv : ∀ h ∈ UWset k r z, h⁻¹ ∈ UWset k r z)
    (hπc : ∀ ξ : Vp, ContinuousOn (fun h => π h ξ) (UWset k r z))
    (hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r)
    (w' w : H) (ξ : Vp) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ g ∈ Gr k r, ∫⁻ p, ‖bInt z c σ π w' ξ (σ g w) p‖ₑ ∂(μW.prod μN) ≤
      ENNReal.ofReal (C * opn g ^ N1H k r))
    {β : Mat k r → ℂ} (hβm : AEStronglyMeasurable (fun g : Mt k r => β (Matrix.of g)) μG)
    (hβw : ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤)
    (hβi : Integrable (fun g : Mt k r => β (Matrix.of g) • σ (Matrix.of g) w) μG)
    (hβr : ∫ g, β (Matrix.of g) • σ (Matrix.of g) w ∂μG = w)
    {x : Mat k r} (hx : x ∈ Gr k r) :
    Integrable (fun g : Mt k r => β (Matrix.of g) • B0 z c σ π μW μN w' ξ (σ (x * Matrix.of g) w)) μG ∧
      ∫ g, β (Matrix.of g) • B0 z c σ π μW μN w' ξ (σ (x * Matrix.of g) w) ∂μG =
        B0 z c σ π μW μN w' ξ (σ x w) := by
  set F : Mt k r × (Mt k r × Mt k r) → Vp :=
    fun q => β (Matrix.of q.1) • bInt z c σ π w' ξ (σ (x * Matrix.of q.1) w) q.2 with hFdef
  have hG : ∀ᵐ g ∂μG, Matrix.of g ∈ Gr k r := ae_gr hGc

  have hq1 : ∀ᵐ q ∂(μG.prod (μW.prod μN)), Matrix.of q.1 ∈ Gr k r :=
    Measure.quasiMeasurePreserving_fst.ae hG
  have hq2 : ∀ᵐ q ∂(μG.prod (μW.prod μN)),
      Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.1 * Matrix.of q.2.2 ∈ Gr k r :=
    Measure.quasiMeasurePreserving_snd.ae hae
  set T : Set (Mt k r × (Mt k r × Mt k r)) := {q | Matrix.of q.1 ∈ Gr k r ∧
    Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.1 * Matrix.of q.2.2 ∈ Gr k r} with hTdef
  have hc1 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.1 : Mat k r) := continuous_fst
  have hc21 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1 : Mat k r) :=
    continuous_fst.comp continuous_snd
  have hc22 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 : Mat k r) :=
    continuous_snd.comp continuous_snd
  have hcm : Continuous fun q : Mt k r × (Mt k r × Mt k r) =>
      (Matrix.of q.2.1 * Matrix.of q.2.2 : Mat k r) := hc21.matrix_mul hc22
  have hcy : Continuous fun q : Mt k r × (Mt k r × Mt k r) =>
      (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1) : Mat k r) :=
    hcm.matrix_mul (continuous_const.matrix_mul hc1)
  have hTc : IsClosed T :=
    (gr_isClosed.preimage hc1).inter ((hUWc.preimage hc21).inter (gr_isClosed.preimage hcm))
  have hTae : ∀ᵐ q ∂(μG.prod (μW.prod μN)), q ∈ T := by
    filter_upwards [hq1, hq2] with q h1 h2
    exact ⟨h1, h2⟩
  set F' : Mt k r × (Mt k r × Mt k r) → Vp := fun q =>
    (⟪w', σ (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1)) w⟫_ℂ *
      star (psiGen k r z c (Matrix.of q.2.2))) • π (Matrix.of q.2.1)⁻¹ ξ with hF'def
  have hF'c : ContinuousOn F' T := by
    have h1 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
        σ (Matrix.of q.2.1 * Matrix.of q.2.2 * (x * Matrix.of q.1)) w) T :=
      (hσ.2.2 w).comp hcy.continuousOn (fun q hq => gr_mul hq.2.2 (gr_mul hx hq.1))
    have hi : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.1)⁻¹) T :=
      inv_contOn.comp hc21.continuousOn (fun q hq => hUWG hq.2.1)
    have h2 : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => π (Matrix.of q.2.1)⁻¹ ξ) T :=
      (hπc ξ).comp hi (fun q hq => hUWinv _ hq.2.1)
    have h3 : Continuous fun q : Mt k r × (Mt k r × Mt k r) => star (psiGen k r z c (Matrix.of q.2.2)) :=
      continuous_star.comp ((psiGen_cont z c).comp hc22)
    exact ((continuousOn_const.inner h1).mul h3.continuousOn).smul h2
  have hF'm : AEStronglyMeasurable F' (μG.prod (μW.prod μN)) := by
    have := hF'c.aestronglyMeasurable (μ := μG.prod (μW.prod μN)) hTc.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hTae] at this
  have hFm : AEStronglyMeasurable F (μG.prod (μW.prod μN)) := by
    refine ((hβm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).smul hF'm).congr ?_
    filter_upwards [hTae] with q hq
    show β (Matrix.of q.1) • F' q = β (Matrix.of q.1) • bInt z c σ π w' ξ (σ (x * Matrix.of q.1) w) q.2
    congr 1
    simp only [hF'def, bInt]
    rw [← sigma_mul hσ hq.2.2 (gr_mul hx hq.1)]

  have hlin : ∫⁻ q, ‖F q‖ₑ ∂(μG.prod (μW.prod μN)) < ⊤ := by
    rw [lintegral_prod _ hFm.enorm]
    calc ∫⁻ g, ∫⁻ p, ‖F (g, p)‖ₑ ∂(μW.prod μN) ∂μG
        = ∫⁻ g, ‖β (Matrix.of g)‖ₑ *
            ∫⁻ p, ‖bInt z c σ π w' ξ (σ (x * Matrix.of g) w) p‖ₑ ∂(μW.prod μN) ∂μG := by
          refine lintegral_congr fun g => ?_
          simp only [hFdef, enorm_smul]
          exact lintegral_const_mul' _ _ enorm_ne_top
      _ ≤ ∫⁻ g, ENNReal.ofReal (C * opn x ^ N1H k r) *
            (‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) ∂μG := by
          apply lintegral_mono_ae
          filter_upwards [hG] with g hg
          have hb := hB _ (gr_mul hx hg)
          have hN := nilradical_half_sum_nonneg (k := k) (r := r)
          have h1 : C * opn (x * Matrix.of g) ^ N1H k r ≤
              C * opn x ^ N1H k r * opn (Matrix.of g) ^ N1H k r := by
            rw [mul_assoc, ← Real.mul_rpow (opn_nonneg _) (opn_nonneg _)]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (opn_nonneg _) (opn_mul _ _) hN) hC
          calc ‖β (Matrix.of g)‖ₑ * ∫⁻ p, ‖bInt z c σ π w' ξ (σ (x * Matrix.of g) w) p‖ₑ ∂(μW.prod μN)
              ≤ ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (C * opn x ^ N1H k r * opn (Matrix.of g) ^ N1H k r) := by
                gcongr
                exact hb.trans (ENNReal.ofReal_le_ofReal h1)
            _ = _ := by
                rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg (opn_nonneg _) _))]
                ring
      _ = ENNReal.ofReal (C * opn x ^ N1H k r) *
            ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hβw
  have hint : Integrable F (μG.prod (μW.prod μN)) := ⟨hFm, hlin⟩
  have hsl : ∀ g : Mt k r, ∫ p, F (g, p) ∂(μW.prod μN) =
      β (Matrix.of g) • B0 z c σ π μW μN w' ξ (σ (x * Matrix.of g) w) := fun g => by
    simp only [hFdef, B0]
    exact integral_smul _ _
  refine ⟨?_, ?_⟩
  · have := hint.integral_prod_left
    simp only [hsl] at this
    exact this
  · have hsw := integral_integral_swap (f := fun g p => F (g, p)) hint
    simp only [hsl] at hsw
    rw [hsw]
    simp only [B0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show ∫ g, F (g, p) ∂μG = bInt z c σ π w' ξ (σ x w) p
    have hcomp : ∀ᵐ g ∂μG, F (g, p) = ((bLin z c σ π w' ξ p).comp (σ x))
        (β (Matrix.of g) • σ (Matrix.of g) w) := by
      filter_upwards [hG] with g hg
      simp only [hFdef, ContinuousLinearMap.comp_apply, map_smul, bLin_apply]
      rw [sigma_mul hσ hx hg]
    rw [integral_congr_ae hcomp, ContinuousLinearMap.integral_comp_comm _ hβi, hβr,
      ContinuousLinearMap.comp_apply, bLin_apply]

end Kernel

/- English proof (translation)
Establish `h1 : IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `h2 : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mat k r | g *ᵥ v = v}` using `fun v => isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`. Establish `e : UWset k r z = {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r} ∩ ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mat k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g : Mat k r | g *ᵥ z = z})`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨ha, hb, hc⟩`. Conclude with `⟨ha, Set.mem_iInter.2 fun a => ⟨(hb a).1, (hb a).2⟩, hc⟩`. Introduce and unpack `⟨ha, hb, hc⟩`. Conclude with `⟨ha, fun a => ⟨(Set.mem_iInter.1 hb a).1, (Set.mem_iInter.1 hb a).2⟩, hc⟩`. Rewrite using `[e]`.

Conclude with `h1.inter ((isClosed_iInter fun a => (h2 _).inter (h2 _)).inter (h2 z))`.
-/
theorem uw_isClosed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have h1 : IsClosed {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mat k r | g *ᵥ v = v} := fun v =>
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  have e : UWset k r z = {g : Mat k r | gᴴ * Hpk k r * g = Hpk k r} ∩
      ((⋂ a : Fin r, ({g : Mat k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
        {g : Mat k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g : Mat k r | g *ᵥ z = z}) := by
    ext g
    constructor
    · rintro ⟨ha, hb, hc⟩
      exact ⟨ha, Set.mem_iInter.2 fun a => ⟨(hb a).1, (hb a).2⟩, hc⟩
    · rintro ⟨ha, hb, hc⟩
      exact ⟨ha, fun a => ⟨(Set.mem_iInter.1 hb a).1, (Set.mem_iInter.1 hb a).2⟩, hc⟩
  rw [e]
  exact h1.inter ((isClosed_iInter fun a => (h2 _).inter (h2 _)).inter (h2 z))

/- English proof (translation)
Establish `h1 : opn (1 : Mat k r) ≤ opn g⁻¹ * opn g`. Rewrite using `[← Matrix.nonsing_inv_mul _ (gr_isUnit hg)]`. Conclude with `opn_mul _ _`. Establish `h2` using `opn_inv_le hg`. Establish `hone : opn (1 : Mat k r) = 1` using `by unfold opn; rw [map_one]; exact norm_one`.

Rewrite `h1` using `[hone]`. Establish `h0` using `opn_nonneg g`. Establish `hH` using `opn_nonneg (Hpk k r)`. Establish `h4 : 1 ≤ (opn (Hpk k r) * opn g) ^ 2`. Use `mul_le_mul_of_nonneg_right h2 h0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : 1 ≤ opn (Hpk k r) * opn g`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Use `pow_lt_one₀ (mul_nonneg hH h0) hlt two_ne_zero` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← Real.mul_rpow hH h0]`. Conclude with `Real.one_le_rpow h3 nilradical_half_sum_nonneg`.
-/
theorem ak_one_le {g : Mat k r} (hg : g ∈ Gr k r) :
    1 ≤ opn (Hpk k r) ^ N1H k r * opn g ^ N1H k r := by
  have h1 : opn (1 : Mat k r) ≤ opn g⁻¹ * opn g := by
    rw [← Matrix.nonsing_inv_mul _ (gr_isUnit hg)]; exact opn_mul _ _
  have h2 := opn_inv_le hg
  have hone : opn (1 : Mat k r) = 1 := by unfold opn; rw [map_one]; exact norm_one
  rw [hone] at h1
  have h0 := opn_nonneg g
  have hH := opn_nonneg (Hpk k r)
  have h4 : 1 ≤ (opn (Hpk k r) * opn g) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 h0
    nlinarith
  have h3 : 1 ≤ opn (Hpk k r) * opn g := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_one₀ (mul_nonneg hH h0) hlt two_ne_zero
    linarith
  rw [← Real.mul_rpow hH h0]
  exact Real.one_le_rpow h3 nilradical_half_sum_nonneg

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `hAB k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ`. Take `⟨hSet, hDS, hHC, _, hμG, _, _, hμW, hμN, _, _⟩` from `hH`. Establish `hz` using `hSet.2.2.1`. Establish `hT` using `hSet.2.2.2.1`. Establish `hσ : IsURepOn (Gr k r) σ` using `hSG k r _ _ H σ hDS`.

Take `⟨hUWG, hNG, hUW, _, _⟩` from `hS k r z c hz hT`. Establish `hπc` using `representation_continuous k r z u Vp π hz hT hHC`. Use `hμG.1` as an intermediate fact. Use `hμW.1` as an intermediate fact. Use `hμN.1` as an intermediate fact.

Establish `hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r`. Establish `h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z` using `Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hμW.2.2.1)`. Establish `h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r` using `Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hμN.2.2.1)`. Use `filter_upwards [h1, h2] with p hp1 hp2`. Conclude with `⟨hp1, gr_mul (hUWG hp1) (hNG hp2)⟩`.

Conclude with `integrable_and_integral_smul_B0_eq z c hσ hμG.2.2.1 (uw_isClosed z) hUWG (fun h hh => (hUW h hh h hh).2.1) hπc hae (σ x₀ w) w ξ hC0 hC hβm hβw hβi hβr hx`.
-/
theorem conv_of (hSG : SigmaG) (hS : SGrp) (hAB : ABound)
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ}
    {b : Fin (2 * r + 2) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
    [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} {w : H}
    {μG μS ν μW μN : Measure (Mt k r)} (hH : Hyp k r z c u v b σ π w μG μS ν μW μN)
    (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) (hCW : CoefWeightedLoc) {x₀ : Mat k r} (hx₀ : x₀ ∈ Gr k r)
    (ξ : Vp) {β : Mat k r → ℂ} (hβm : AEStronglyMeasurable (fun g : Mt k r => β (Matrix.of g)) μG)
    (hβw : ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤)
    (hβi : Integrable (fun g : Mt k r => β (Matrix.of g) • σ (Matrix.of g) w) μG)
    (hβr : ∫ g, β (Matrix.of g) • σ (Matrix.of g) w ∂μG = w) {x : Mat k r} (hx : x ∈ Gr k r) :
    Integrable (fun g : Mt k r => β (Matrix.of g) • (Af z c σ π μW μN w x₀ ξ) (x * Matrix.of g)) μG ∧
      rconv μG β (Af z c σ π μW μN w x₀ ξ) x = (Af z c σ π μW μN w x₀ ξ) x := by
  obtain ⟨C, hC0, hC⟩ := hAB k r z c u v b H σ Vp π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ
  obtain ⟨hSet, hDS, hHC, _, hμG, _, _, hμW, hμN, _, _⟩ := hH
  have hz := hSet.2.2.1
  have hT := hSet.2.2.2.1
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨hUWG, hNG, hUW, _, _⟩ := hS k r z c hz hT
  have hπc := representation_continuous k r z u Vp π hz hT hHC
  have := hμG.1
  have := hμW.1
  have := hμN.1
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.1 * Matrix.of p.2 ∈ Gr k r := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hμW.2.2.1)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hμN.2.2.1)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, gr_mul (hUWG hp1) (hNG hp2)⟩
  exact integrable_and_integral_smul_B0_eq z c hσ hμG.2.2.1 (uw_isClosed z) hUWG (fun h hh => (hUW h hh h hh).2.1) hπc hae
    (σ x₀ w) w ξ hC0 hC hβm hβw hβi hβr hx

/- English proof (translation)
Establish `hGae` using `ae_gr hGc`. Establish `hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`. Establish `hsm : AEStronglyMeasurable (fun g : Mt k r => σ (Matrix.of g) w) μG`. Establish `hcl : IsClosed {g : Mt k r | Matrix.of g ∈ Gr k r}` using `gr_isClosed.preimage hof`. Use `((hσ.2.2 w).comp hof.continuousOn (fun g hg => hg)).aestronglyMeasurable (μ := μG) hcl.measurableSet` as an intermediate fact.

Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem hGae]`. Conclude with `this`. Use `⟨hβm.smul hsm, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ g, ‖β (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG < ⊤`. Combine the equalities or inequalities in the displayed calculation.

Apply `lintegral_mono_ae` to reduce the goal to its premises. Use `filter_upwards [hGae] with g hg`. Rewrite using `[enorm_smul, ← ofReal_norm (σ _ w), hσ.2.1 _ hg, hw1, ENNReal.ofReal_one, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = ENNReal.ofReal (opn (Hpk k r) ^ N1H k r) * ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`.

Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hβw`.
-/
theorem smul_int {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (Gr k r) σ) {μG : Measure (Mt k r)}
    (hGc : μG {x | Matrix.of x ∉ Gr k r} = 0) {w : H} (hw1 : ‖w‖ = 1) {β : Mat k r → ℂ}
    (hβm : AEStronglyMeasurable (fun g : Mt k r => β (Matrix.of g)) μG)
    (hβw : ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤) :
    Integrable (fun g : Mt k r => β (Matrix.of g) • σ (Matrix.of g) w) μG := by
  have hGae := ae_gr hGc
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hsm : AEStronglyMeasurable (fun g : Mt k r => σ (Matrix.of g) w) μG := by
    have hcl : IsClosed {g : Mt k r | Matrix.of g ∈ Gr k r} := gr_isClosed.preimage hof
    have := ((hσ.2.2 w).comp hof.continuousOn (fun g hg => hg)).aestronglyMeasurable (μ := μG)
      hcl.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hGae] at this
    exact this
  refine ⟨hβm.smul hsm, ?_⟩
  show ∫⁻ g, ‖β (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG < ⊤
  calc ∫⁻ g, ‖β (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG
      ≤ ∫⁻ g, ENNReal.ofReal (opn (Hpk k r) ^ N1H k r) *
          (‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) ∂μG := by
        apply lintegral_mono_ae
        filter_upwards [hGae] with g hg
        rw [enorm_smul, ← ofReal_norm (σ _ w), hσ.2.1 _ hg, hw1, ENNReal.ofReal_one, mul_one]
        calc ‖β (Matrix.of g)‖ₑ = ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal 1 := by simp
          _ ≤ ‖β (Matrix.of g)‖ₑ *
              ENNReal.ofReal (opn (Hpk k r) ^ N1H k r * opn (Matrix.of g) ^ N1H k r) := by
            gcongr; exact ak_one_le hg
          _ = _ := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg (opn_nonneg _) _)]; ring
    _ = ENNReal.ofReal (opn (Hpk k r) ^ N1H k r) *
          ∫⁻ g, ‖β (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hβw

/- English proof (translation)
Introduce `k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ x hx`. Establish `hdec` using `hD hCW k r z c u v b H σ Vp π w μG μS ν μW μN hH`. Take `⟨d, hd, hSc⟩` from `hSch k r z c u v b H σ Vp π w μG μS ν μW μN hH`. Establish `hH'` using `hH`. Take `⟨_, hDS, _, hLow, hμG, _⟩` from `hH'`.

Establish `hσ : IsURepOn (Gr k r) σ` using `hSG k r _ _ H σ hDS`. Take `⟨_, _, hw1, _⟩` from `hLow`. Establish `hGae` using `ae_gr hμG.2.2.1`. Establish `hww : ⟪w, w⟫_ℂ = 1` using `by rw [inner_self_eq_norm_sq_to_K, hw1]; simp`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`.

Establish `hfd : fdegH μG σ w = d`. Establish `h` using `(hSc w w w w).2`. Rewrite `h` using `[hww]`. Establish `h2 : ∀ g : Mt k r, ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ)` using `fun g => by`. Rewrite using `[Complex.ofReal_pow]`.

Conclude with `RCLike.mul_conj _`. Rewrite `h` using `[h2]`. Rewrite `h` using `[integral_complex_ofReal]`. Establish `h3 : ((∫ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ)`. Rewrite using `[h]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ∫ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d` using `by exact_mod_cast h3`. Unfold `fdegH`. Rewrite using `[h4, hw1]`.

Clear the denominators using the available nonvanishing facts. Establish `hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`. Establish `hcl : IsClosed {g : Mt k r | Matrix.of g ∈ Gr k r}` using `gr_isClosed.preimage hof`. Establish `hβm : AEStronglyMeasurable (fun g : Mt k r => eFun μG σ w (Matrix.of g)) μG`. Establish `hc : ContinuousOn (fun g : Mt k r => eFun μG σ w (Matrix.of g)) {g | Matrix.of g ∈ Gr k r}` using `continuousOn_const.mul (continuous_star.comp_continuousOn (continuousOn_const.inner ((hσ.2.2 w).comp hof.continuousOn (fun g hg => hg))))`.

Use `hc.aestronglyMeasurable (μ := μG) hcl.measurableSet` as an intermediate fact. Rewrite `this` using `[Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ Gr k r}) hGae]`. Conclude with `this`. Establish `hnorm : ∀ g : Mt k r, ‖eFun μG σ w (Matrix.of g)‖ₑ = ‖(d : ℂ)‖ₑ * ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ`. Introduce `g`.

Unfold `eFun`. Rewrite using `[hfd, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]`. Establish `hβw : ∫⁻ g, ‖eFun μG σ w (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun g => ?_` and prove the remaining obligations.

Rewrite using `[hnorm, mul_assoc]`. Use `_ = ‖(d : ℂ)‖ₑ * ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG := lintegral_const_mul' _ _ enorm_ne_top`. Use `_ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hdec`. Establish `hβi` using `smul_int hσ hμG.2.2.1 hw1 hβm hβw`. Establish `hβr : ∫ g, eFun μG σ w (Matrix.of g) • σ (Matrix.of g) w ∂μG = w`.

Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `v'`. Rewrite using `[← integral_inner hβi v']`. Repeatedly rewrite using `[inner_smul_right]`. Establish `he : ∀ g : Mt k r, eFun μG σ w (Matrix.of g) * ⟪v', σ (Matrix.of g) w⟫_ℂ = (d : ℂ) * (⟪v', σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ)`.

Introduce `g`. Unfold `eFun`. Rewrite using `[hfd]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[he]`.

Rewrite using `[integral_const_mul, (hSc w v' w w).2, hww]`. Clear the denominators using the available nonvanishing facts. Conclude with `conv_of hSG hS hAB hH hR hCW hx₀ ξ hβm hβw hβi hβr hx`.
-/
theorem aKind_of (hSG : SigmaG) (hS : SGrp) (hAB : ABound) (hD : Decay)
    (hSch : SchurG) : AKind := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ x hx
  have hdec := hD hCW k r z c u v b H σ Vp π w μG μS ν μW μN hH
  obtain ⟨d, hd, hSc⟩ := hSch k r z c u v b H σ Vp π w μG μS ν μW μN hH
  have hH' := hH
  obtain ⟨_, hDS, _, hLow, hμG, _⟩ := hH'
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨_, _, hw1, _⟩ := hLow
  have hGae := ae_gr hμG.2.2.1
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfd : fdegH μG σ w = d := by
    have h := (hSc w w w w).2
    rw [hww] at h
    have h2 : ∀ g : Mt k r, ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ =
        ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun g => by
      rw [Complex.ofReal_pow]; exact RCLike.mul_conj _
    simp_rw [h2] at h
    rw [integral_complex_ofReal] at h
    have h3 : ((∫ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    have h4 : ∫ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by exact_mod_cast h3
    unfold fdegH
    rw [h4, hw1]
    field_simp
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hcl : IsClosed {g : Mt k r | Matrix.of g ∈ Gr k r} := gr_isClosed.preimage hof
  have hβm : AEStronglyMeasurable (fun g : Mt k r => eFun μG σ w (Matrix.of g)) μG := by
    have hc : ContinuousOn (fun g : Mt k r => eFun μG σ w (Matrix.of g)) {g | Matrix.of g ∈ Gr k r} :=
      continuousOn_const.mul (continuous_star.comp_continuousOn (continuousOn_const.inner
        ((hσ.2.2 w).comp hof.continuousOn (fun g hg => hg))))
    have := hc.aestronglyMeasurable (μ := μG) hcl.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ Gr k r}) hGae] at this
    exact this
  have hnorm : ∀ g : Mt k r, ‖eFun μG σ w (Matrix.of g)‖ₑ = ‖(d : ℂ)‖ₑ * ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ := by
    intro g
    unfold eFun
    rw [hfd, enorm_mul, ← ofReal_norm (star _), norm_star, ofReal_norm]
  have hβw : ∫⁻ g, ‖eFun μG σ w (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤ := by
    calc ∫⁻ g, ‖eFun μG σ w (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG
        = ∫⁻ g, ‖(d : ℂ)‖ₑ * (‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r)) ∂μG := by
          refine lintegral_congr fun g => ?_
          rw [hnorm, mul_assoc]
      _ = ‖(d : ℂ)‖ₑ * ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ *
            ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG :=
          lintegral_const_mul' _ _ enorm_ne_top
      _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hdec
  have hβi := smul_int hσ hμG.2.2.1 hw1 hβm hβw
  have hβr : ∫ g, eFun μG σ w (Matrix.of g) • σ (Matrix.of g) w ∂μG = w := by
    apply ext_inner_left ℂ
    intro v'
    rw [← integral_inner hβi v']
    simp_rw [inner_smul_right]
    have he : ∀ g : Mt k r, eFun μG σ w (Matrix.of g) * ⟪v', σ (Matrix.of g) w⟫_ℂ =
        (d : ℂ) * (⟪v', σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) := by
      intro g; unfold eFun; rw [hfd]; ring
    simp_rw [he]
    rw [integral_const_mul, (hSc w v' w w).2, hww]
    field_simp
  exact conv_of hSG hS hAB hH hR hCW hx₀ ξ hβm hβw hβi hβr hx

/- English proof (translation)
Introduce `k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ`. Take `⟨α, Ω, a, hΩ, hΩG, hαm, hsupp, hbd, hint, hrep⟩` from `hRG hR k r z c u v b H σ Vp π w μG μS ν μW μN hH`. Establish `hH'` using `hH`. Take `⟨_, hDS, _, hLow, hμG, _⟩` from `hH'`. Establish `hσ : IsURepOn (Gr k r) σ` using `hSG k r _ _ H σ hDS`.

Take `⟨_, _, hw1, _⟩` from `hLow`. Establish `hGae` using `ae_gr hμG.2.2.1`. Take `⟨K, hK⟩` from `hΩ.exists_bound_of_continuousOn (opn_continuous (k := k) (r := r)).continuousOn`. Establish `hw : ∫⁻ g, ‖α (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤`. Combine the equalities or inequalities in the displayed calculation.

Apply `lintegral_mono_ae` to reduce the goal to its premises. Use `filter_upwards [hGae] with g hg`. Rewrite using `[enorm_smul, ← ofReal_norm (σ _ w), hσ.2.1 _ hg, hw1, ENNReal.ofReal_one, mul_one]`. Distinguish the cases in `h0 : α (Matrix.of g) = 0`. Simplify using `[h0]`.

Conclude with `(mul_comm _ _).trans_le (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (opn_nonneg _) (((Real.le_norm_self _).trans (hK _ (hsupp _ h0))).trans (le_max_left _ _)) nilradical_half_sum_nonneg)) le_rfl)`. Use `_ = ENNReal.ofReal (max K 0 ^ N1H k r) * ∫⁻ g, ‖α (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.2`. Use `⟨α, Ω ∪ {1}, a, hΩ.union isCompact_singleton, Set.mem_union_right _ rfl, Set.union_subset hΩG (Set.singleton_subset_iff.2 gr_one), hαm, fun y hy => Or.inl (hsupp y hy), hbd, fun x hx => ?_⟩` and prove the remaining obligations. Conclude with `conv_of hSG hS hAB hH hR hCW hx₀ ξ hαm.aestronglyMeasurable hw hint hrep hx`.
-/
theorem aReprod_of (hSG : SigmaG) (hS : SGrp) (hAB : ABound) (hRG : ReprodG) :
    AReprod := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hH hR hCW x₀ hx₀ ξ
  obtain ⟨α, Ω, a, hΩ, hΩG, hαm, hsupp, hbd, hint, hrep⟩ :=
    hRG hR k r z c u v b H σ Vp π w μG μS ν μW μN hH
  have hH' := hH
  obtain ⟨_, hDS, _, hLow, hμG, _⟩ := hH'
  have hσ : IsURepOn (Gr k r) σ := hSG k r _ _ H σ hDS
  obtain ⟨_, _, hw1, _⟩ := hLow
  have hGae := ae_gr hμG.2.2.1
  obtain ⟨K, hK⟩ := hΩ.exists_bound_of_continuousOn (opn_continuous (k := k) (r := r)).continuousOn
  have hw : ∫⁻ g, ‖α (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG < ⊤ := by
    calc ∫⁻ g, ‖α (Matrix.of g)‖ₑ * ENNReal.ofReal (opn (Matrix.of g) ^ N1H k r) ∂μG
        ≤ ∫⁻ g, ENNReal.ofReal (max K 0 ^ N1H k r) * ‖α (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG := by
          apply lintegral_mono_ae
          filter_upwards [hGae] with g hg
          rw [enorm_smul, ← ofReal_norm (σ _ w), hσ.2.1 _ hg, hw1, ENNReal.ofReal_one, mul_one]
          by_cases h0 : α (Matrix.of g) = 0
          · simp [h0]
          · exact (mul_comm _ _).trans_le (mul_le_mul' (ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (opn_nonneg _)
                (((Real.le_norm_self _).trans (hK _ (hsupp _ h0))).trans (le_max_left _ _)) nilradical_half_sum_nonneg)) le_rfl)
      _ = ENNReal.ofReal (max K 0 ^ N1H k r) * ∫⁻ g, ‖α (Matrix.of g) • σ (Matrix.of g) w‖ₑ ∂μG :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint.2
  refine ⟨α, Ω ∪ {1}, a, hΩ.union isCompact_singleton, Set.mem_union_right _ rfl,
    Set.union_subset hΩG (Set.singleton_subset_iff.2 gr_one), hαm, fun y hy => Or.inl (hsupp y hy),
    hbd, fun x hx => ?_⟩
  exact conv_of hSG hS hAB hH hR hCW hx₀ ξ hαm.aestronglyMeasurable hw hint hrep hx

end WlocSk.AK
