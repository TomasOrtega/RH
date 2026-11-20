import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RsWhittaker

open Ad3 Ad3.R

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(uni2 x : GL (Fin 2) 𝔸[ℚ]).val a b = unipMatrix (n := 2) (r := 1) (fun _ => x) a b`. Rewrite using `[unipMatrix_apply]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [uni2]`.
-/
theorem unipotent_eq_adelic_unipotent (x : 𝔸[ℚ]) : (uni2 x : G2) = unipAdele x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change (uni2 x : GL (Fin 2) 𝔸[ℚ]).val a b = unipMatrix (n := 2) (r := 1) (fun _ => x) a b
  rw [unipMatrix_apply]
  fin_cases a <;> fin_cases b <;> simp [uni2]

/- English proof (translation)
Simplify using `only [unipotent_eq_adelic_unipotent, unipAdele_add]`.
-/
theorem unipotent_add (x y : 𝔸[ℚ]) : (uni2 (x + y) : G2) = uni2 x * uni2 y := by
  simp only [unipotent_eq_adelic_unipotent, unipAdele_add]

/- English proof (translation)
Rewrite using `[unipotent_eq_adelic_unipotent, unipAdele_algebraMap]`. Use `congr 1`. Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => q) a b = _`. Rewrite using `[unipMatrix_apply]`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [uni2]`.
-/
theorem unipotent_rational_eq_diagonal (q : ℚ) : (uni2 (algebraMap ℚ 𝔸[ℚ] q) : G2) = dia2 (uni2 q) := by
  rw [unipotent_eq_adelic_unipotent, unipAdele_algebraMap]
  congr 1
  refine Units.ext (Matrix.ext fun a b => ?_)
  change unipMatrix (n := 2) (r := 1) (fun _ => q) a b = _
  rw [unipMatrix_apply]
  fin_cases a <;> fin_cases b <;> simp [uni2]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`.
-/
theorem central_comm (x : 𝔸[ℚ]) (z : Jd) : (uni2 x : G2) * dg2 z z = dg2 z z * uni2 x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  fin_cases a <;> fin_cases b <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/- English proof (translation)
Simplify using `only [Wh]`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[← mul_assoc, central_comm, mul_assoc, h, mul_assoc]`.
-/
theorem wh_central {φ : G2 → ℂ} {c : Jd → ℂ} (h : ∀ (z : Jd) g, φ (dg2 z z * g) = c z * φ g) (z : Jd) (g : G2) :
    Wh φ (dg2 z z * g) = c z * Wh φ g := by
  simp only [Wh]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only []
  rw [← mul_assoc, central_comm, mul_assoc, h, mul_assoc]

/- English proof (translation)
Take `⟨_, q, rfl⟩` from `ξ`. Express the relevant statement in the definitionally equal form `φ (uni2 (algebraMap ℚ 𝔸[ℚ] q + x) * g) * (adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] q + x)) : ℂ) = _`. Rewrite using `[unipotent_add, unipotent_rational_eq_diagonal, mul_assoc, hφ, neg_add, AddChar.map_add_eq_mul, ← map_neg, adelicChar_algebraMap, one_mul]`.
-/
theorem wh_integrand_vadd {φ : G2 → ℂ} (hφ : LInv φ) (g : G2)
    (ξ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸[ℚ]) :
    φ (uni2 (ξ +ᵥ x) * g) * (adelicChar ℚ (-(ξ +ᵥ x)) : ℂ) = φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) := by
  obtain ⟨_, q, rfl⟩ := ξ
  change φ (uni2 (algebraMap ℚ 𝔸[ℚ] q + x) * g) * (adelicChar ℚ (-(algebraMap ℚ 𝔸[ℚ] q + x)) : ℂ) = _
  rw [unipotent_add, unipotent_rational_eq_diagonal, mul_assoc, hφ, neg_add, AddChar.map_add_eq_mul, ← map_neg,
    adelicChar_algebraMap, one_mul]

open scoped Pointwise in
/- English proof (translation)
Use `set h : 𝔸[ℚ] → ℂ := fun x => φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) with hh`. Establish `hF` using `isAddFundamentalDomain_fundamentalSet ℚ`. Establish `hinv : ∀ (ξ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸[ℚ]), h (ξ +ᵥ x) = h x` using `wh_integrand_vadd hφ g`. Establish `hD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y +ᵥ fundamentalSet ℚ) (adeleMeasure ℚ)` using `hF.vadd_of_comm y`. Establish `e1 : ∫ x in fundamentalSet ℚ, h (x + y) ∂adeleMeasure ℚ = ∫ x in fundamentalSet ℚ, h x ∂adeleMeasure ℚ`.

Rewrite using `[hF.setIntegral_eq hD hinv]`. Use `(measurePreserving_add_right (adeleMeasure ℚ) y).setIntegral_preimage_emb (measurableEmbedding_addRight y) h (y +ᵥ fundamentalSet ℚ)` as an intermediate fact. Rewrite using `[← this]`. Establish `hs : (fun x => x + y) ⁻¹' (y +ᵥ fundamentalSet ℚ) = fundamentalSet ℚ`. Use extensionality with `x`.

Simplify using `[Set.mem_vadd_set, add_comm]`. Rewrite using `[hs]`. Simplify using `only [Wh]`. Rewrite using `[← e1, ← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations.

Simplify using `only [hh]`. Rewrite using `[← mul_assoc, ← unipotent_add, neg_add, AddChar.map_add_eq_mul]`. Establish `hc : ((adelicChar ℚ y : Circle) : ℂ) * ((adelicChar ℚ (-y) : Circle) : ℂ) = 1`. Rewrite using `[← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]`. Rewrite using `[Circle.coe_mul]`.

Take the linear combination `(-(φ (uni2 (x + y) * g)) * ((adelicChar ℚ (-x) : Circle) : ℂ)) * hc`.
-/
theorem wh_law {φ : G2 → ℂ} (hφ : LInv φ) (y : 𝔸[ℚ]) (g : G2) :
    Wh φ (uni2 y * g) = (adelicChar ℚ y : ℂ) * Wh φ g := by
  set h : 𝔸[ℚ] → ℂ := fun x => φ (uni2 x * g) * (adelicChar ℚ (-x) : ℂ) with hh
  have hF := isAddFundamentalDomain_fundamentalSet ℚ
  have hinv : ∀ (ξ : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸[ℚ]), h (ξ +ᵥ x) = h x :=
    wh_integrand_vadd hφ g
  have hD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (y +ᵥ fundamentalSet ℚ)
      (adeleMeasure ℚ) := hF.vadd_of_comm y
  have e1 : ∫ x in fundamentalSet ℚ, h (x + y) ∂adeleMeasure ℚ = ∫ x in fundamentalSet ℚ, h x ∂adeleMeasure ℚ := by
    rw [hF.setIntegral_eq hD hinv]
    have := (measurePreserving_add_right (adeleMeasure ℚ) y).setIntegral_preimage_emb
      (measurableEmbedding_addRight y) h (y +ᵥ fundamentalSet ℚ)
    rw [← this]
    have hs : (fun x => x + y) ⁻¹' (y +ᵥ fundamentalSet ℚ) = fundamentalSet ℚ := by
      ext x
      simp [Set.mem_vadd_set, add_comm]
    rw [hs]
  simp only [Wh]
  rw [← e1, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [hh]
  rw [← mul_assoc, ← unipotent_add, neg_add, AddChar.map_add_eq_mul]
  have hc : ((adelicChar ℚ y : Circle) : ℂ) * ((adelicChar ℚ (-y) : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  rw [Circle.coe_mul]
  linear_combination (-(φ (uni2 (x + y) * g)) * ((adelicChar ℚ (-x) : Circle) : ℂ)) * hc

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun a b => ?_ fin_cases a <;> fin_cases b <;> simp [uni2, Function.comp_def] <;> fun_prop`. Express the relevant statement in the definitionally equal form `Continuous fun x : 𝔸[ℚ] => ((uni2 x : G2)⁻¹).val`. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [uni2, Function.comp_def] <;> fun_prop`.
-/
theorem continuous_unipotentGL2 : Continuous (fun x : 𝔸[ℚ] => (uni2 x : G2)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [uni2, Function.comp_def] <;> fun_prop
  · change Continuous fun x : 𝔸[ℚ] => ((uni2 x : G2)⁻¹).val
    refine continuous_matrix fun a b => ?_
    fin_cases a <;> fin_cases b <;> simp [uni2, Function.comp_def] <;> fun_prop

/- English proof (translation)
The claim follows from `(isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ)`.
-/
theorem isCompact_box : IsCompact (closure (fundamentalSetInfinite ℚ) ×ˢ
    (integralFiniteAdeles (𝓞 ℚ) ℚ : Set 𝔸f) : Set 𝔸[ℚ]) :=
  (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ)

/- English proof (translation)
The claim follows from `Set.prod_mono subset_closure subset_rfl`.
-/
theorem fundamentalSet_subset_box : fundamentalSet ℚ ⊆ (closure (fundamentalSetInfinite ℚ) ×ˢ
    (integralFiniteAdeles (𝓞 ℚ) ℚ : Set 𝔸f) : Set 𝔸[ℚ]) :=
  Set.prod_mono subset_closure subset_rfl

/- English proof (translation)
Establish `hint : ∀ g : X, IntegrableOn (fun x => H (g, x)) F μ` using `fun g => ((hHc.comp (Continuous.prodMk_right g)).continuousOn.integrableOn_compact hCc).mono_set hFC`. Establish `hFt : μ F < ∞` using `(measure_mono hFC).trans_lt hCc.measure_lt_top`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`.

Introduce `ε hε`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * μ.real F < ε := by`. Use `⟨ε / (μ.real F + 1), by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]`. Establish `: 0 ≤ μ.real F` using `measureReal_nonneg`.

Use the polynomial consequences of the given equalities and inequalities. Use `set n : Set (X × Y) := {p | ‖H p - H (g₀, p.2)‖ < δ} with hn`. Establish `hno : IsOpen n`. Use `isOpen_lt (Continuous.norm (hHc.sub (hHc.comp ?_))) continuous_const` and prove the remaining obligations. Conclude with `continuous_const.prodMk continuous_snd`.

Establish `hsub : ({g₀} : Set X) ×ˢ C ⊆ n`. Introduce and unpack `⟨g, x⟩ ⟨hg, -⟩`. Take `rfl : g = g₀` from `hg`. Simplify `hδ` using `[hn]`. Take `⟨u, v, hu, -, hgu, hCv, huv⟩` from `generalized_tube_lemma isCompact_singleton hCc hno hsub`.

Use `Filter.eventually_of_mem (hu.mem_nhds (hgu rfl)) fun g hg => ?_` and prove the remaining obligations. Establish `hb : ∀ x ∈ F, ‖H (g, x) - H (g₀, x)‖ ≤ δ` using `fun x hx => (huv (Set.mk_mem_prod hg (hCv (hFC hx))) : _ < _).le`. Establish `key` using `norm_setIntegral_le_of_norm_le_const (μ := μ) (s := F) (f := fun x => H (g, x) - H (g₀, x)) (C := δ) hFt hb`. Rewrite `key` using `[integral_sub (hint g) (hint g₀)]`. Rewrite using `[dist_eq_norm]`.

Conclude with `key.trans_lt hδε`.
-/
theorem continuous_setIntegral_of_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    {H : X × Y → ℂ} (hHc : Continuous H) {F C : Set Y} (hCc : IsCompact C) (hFC : F ⊆ C) :
    Continuous (fun g => ∫ x in F, H (g, x) ∂μ) := by
  have hint : ∀ g : X, IntegrableOn (fun x => H (g, x)) F μ := fun g =>
    ((hHc.comp (Continuous.prodMk_right g)).continuousOn.integrableOn_compact hCc).mono_set hFC
  have hFt : μ F < ∞ := (measure_mono hFC).trans_lt hCc.measure_lt_top
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * μ.real F < ε := by
    refine ⟨ε / (μ.real F + 1), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    have : 0 ≤ μ.real F := measureReal_nonneg
    nlinarith
  set n : Set (X × Y) := {p | ‖H p - H (g₀, p.2)‖ < δ} with hn
  have hno : IsOpen n := by
    refine isOpen_lt (Continuous.norm (hHc.sub (hHc.comp ?_))) continuous_const
    exact continuous_const.prodMk continuous_snd
  have hsub : ({g₀} : Set X) ×ˢ C ⊆ n := by
    rintro ⟨g, x⟩ ⟨hg, -⟩
    obtain rfl : g = g₀ := hg
    simpa [hn] using hδ
  obtain ⟨u, v, hu, -, hgu, hCv, huv⟩ := generalized_tube_lemma isCompact_singleton hCc hno hsub
  refine Filter.eventually_of_mem (hu.mem_nhds (hgu rfl)) fun g hg => ?_
  have hb : ∀ x ∈ F, ‖H (g, x) - H (g₀, x)‖ ≤ δ := fun x hx =>
    (huv (Set.mk_mem_prod hg (hCv (hFC hx))) : _ < _).le
  have key := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := F)
    (f := fun x => H (g, x) - H (g₀, x)) (C := δ) hFt hb
  rw [integral_sub (hint g) (hint g₀)] at key
  rw [dist_eq_norm]
  exact key.trans_lt hδε

/- English proof (translation)
Establish `hHc : Continuous (fun p : G2 × 𝔸[ℚ] => φ (uni2 p.2 * p.1) * (adelicChar ℚ (-p.2) : ℂ))`. Use `(hφ.comp ((continuous_unipotentGL2.comp continuous_snd).mul continuous_fst)).mul ?_` and prove the remaining obligations. Conclude with `continuous_induced_dom.comp ((continuous_adelicChar (K := ℚ)).comp continuous_snd.neg)`. Conclude with `continuous_setIntegral_of_compact (adeleMeasure ℚ) hHc isCompact_box fundamentalSet_subset_box`.
-/
theorem wh_continuous {φ : G2 → ℂ} (hφ : Continuous φ) : Continuous (Wh φ) := by
  have hHc : Continuous (fun p : G2 × 𝔸[ℚ] => φ (uni2 p.2 * p.1) * (adelicChar ℚ (-p.2) : ℂ)) := by
    refine (hφ.comp ((continuous_unipotentGL2.comp continuous_snd).mul continuous_fst)).mul ?_
    exact continuous_induced_dom.comp ((continuous_adelicChar (K := ℚ)).comp continuous_snd.neg)
  exact continuous_setIntegral_of_compact (adeleMeasure ℚ) hHc isCompact_box fundamentalSet_subset_box

/- English proof (translation)
Rewrite using `[infiniteTrace_apply, Fintype.sum_unique, InfinitePlace.mult_isReal ⟨_, RationalIdeles.isReal_infinitePlace default⟩, Nat.cast_one, one_mul, RationalIdeles.realEquiv_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (RationalIdeles.isReal_infinitePlace default), …`.
-/
theorem infiniteTrace_eq (x : InfiniteAdeleRing ℚ) : infiniteTrace ℚ x = RationalIdeles.realEquiv x := by
  rw [infiniteTrace_apply, Fintype.sum_unique, InfinitePlace.mult_isReal ⟨_, RationalIdeles.isReal_infinitePlace default⟩,
    Nat.cast_one, one_mul, RationalIdeles.realEquiv_apply,
    ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (RationalIdeles.isReal_infinitePlace default), Complex.ofReal_re]

/- English proof (translation)
Establish `hm : -x ∈ invDifferentAdeles ℚ` using `mem_invDifferentAdeles.2 (neg_mem (mem_finiteInvDifferent_of_mem_integralFiniteAdeles hx))`. Rewrite using `[adelicChar_of_mem_invDifferentAdeles hm, Real.fourierChar_apply]`. Establish `: -(infiniteTrace ℚ (-x).1) = RationalIdeles.realEquiv x.1`. Rewrite using `[infiniteTrace_eq]`. Express the relevant statement in the definitionally equal form `-(RationalIdeles.realEquiv (-x.1)) = _`.

Rewrite using `[map_neg, neg_neg]`. Rewrite using `[this]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adelicChar_neg_of_integral {x : 𝔸[ℚ]} (hx : x.2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ((adelicChar ℚ (-x) : Circle) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (RationalIdeles.realEquiv x.1 : ℝ)) := by
  have hm : -x ∈ invDifferentAdeles ℚ := mem_invDifferentAdeles.2
    (neg_mem (mem_finiteInvDifferent_of_mem_integralFiniteAdeles hx))
  rw [adelicChar_of_mem_invDifferentAdeles hm, Real.fourierChar_apply]
  have : -(infiniteTrace ℚ (-x).1) = RationalIdeles.realEquiv x.1 := by
    rw [infiniteTrace_eq]
    change -(RationalIdeles.realEquiv (-x.1)) = _
    rw [map_neg, neg_neg]
  rw [this]
  congr 1
  push_cast
  ring

/- English proof (translation)
Use `set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) (1 : ℕ)`. Combine the equalities or inequalities in the displayed calculation. Establish `hf` using `integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A) (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal 1)) (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))`. Rewrite using `[← Measure.prod_restrict]`. Use `hf.trans ?_` and prove the remaining obligations.

Rewrite using `[measureReal_restrict_apply_univ, measureReal_def]`. Use `_ = (finiteAdeleMeasure ℚ (levelIdeal 1)).toReal • ∫ t in Set.Ico (0 : ℝ) (1 : ℕ), G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by`. Use `congr 1`. Conclude with `(realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ) G (Set.Ico (0 : ℝ) (1 : ℕ))).symm`. Use `_ = levelConstant 1 • ∫ t in (0 : ℝ)..1, G t := by`.

Rewrite using `[map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure, intervalIntegral.integral_of_le zero_le_one, Nat.cast_one, integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]`.
-/
theorem setIntegral_levelDomain (G : ℝ → ℂ) :
    ∫ x in levelDomain 1, G (RationalIdeles.realEquiv x.1) ∂adeleMeasure ℚ =
      levelConstant 1 • ∫ t in (0 : ℝ)..1, G t := by
  set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) (1 : ℕ)
  calc ∫ x in levelDomain 1, G (RationalIdeles.realEquiv x.1) ∂adeleMeasure ℚ
      = ∫ x in (A ×ˢ levelIdeal 1 : Set (InfiniteAdeleRing ℚ × 𝔸f)), G (RationalIdeles.realEquiv x.1)
          ∂((infiniteAdeleMeasure ℚ).prod (finiteAdeleMeasure ℚ)) := rfl
    _ = (finiteAdeleMeasure ℚ (levelIdeal 1)).toReal •
          ∫ x in A, G (RationalIdeles.realEquiv x) ∂infiniteAdeleMeasure ℚ := by
        have hf := integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A)
          (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal 1))
          (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))
        rw [← Measure.prod_restrict]
        refine hf.trans ?_
        rw [measureReal_restrict_apply_univ, measureReal_def]
    _ = (finiteAdeleMeasure ℚ (levelIdeal 1)).toReal •
          ∫ t in Set.Ico (0 : ℝ) (1 : ℕ), G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by
        congr 1
        exact (realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ)
          G (Set.Ico (0 : ℝ) (1 : ℕ))).symm
    _ = levelConstant 1 • ∫ t in (0 : ℝ)..1, G t := by
        rw [map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
          intervalIntegral.integral_of_le zero_le_one, Nat.cast_one, integral_Ico_eq_integral_Ioo,
          ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]

/- English proof (translation)
Establish `h1` using `setIntegral_levelDomain (fun _ => (1 : ℂ))`. Establish `hm : adeleMeasure ℚ (levelDomain 1) = 1`. Rewrite using `[← (isAddFundamentalDomain_fundamentalSet ℚ).measure_eq (isAddFundamentalDomain_levelDomain 1)]`. Conclude with `adeleMeasure_fundamentalSet ℚ`. Simplify using `only [intervalIntegral.integral_const, sub_zero, one_smul, integral_const, measureReal_restrict_apply_univ, measureReal_def, hm] at h1`.

Simplify `h1.symm` using `[hm]`.
-/
theorem levelConstant_one : levelConstant 1 = 1 := by
  have h1 := setIntegral_levelDomain (fun _ => (1 : ℂ))
  have hm : adeleMeasure ℚ (levelDomain 1) = 1 := by
    rw [← (isAddFundamentalDomain_fundamentalSet ℚ).measure_eq (isAddFundamentalDomain_levelDomain 1)]
    exact adeleMeasure_fundamentalSet ℚ
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, integral_const, measureReal_restrict_apply_univ, measureReal_def, hm] at h1
  simpa [hm] using h1.symm

/- English proof (translation)
Establish `e1 : Wh φ (realEmb h) = ∫ x in levelDomain 1, φ (uni2 x * realEmb h) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ` using `(isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq (isAddFundamentalDomain_levelDomain 1) (wh_integrand_vadd hL _)`. Rewrite using `[e1]`. Use `set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h)) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) with hG`. Establish `heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (uni2 x * realEmb h) * (adelicChar ℚ (-x) : ℂ)) (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain 1)`. Introduce `x hx`.

Establish `hxZ : x.2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ` using `levelIdeal_subset 1 hx.2`. Simplify using `only [hG]`. Rewrite using `[adelicChar_neg_of_integral hxZ, unipotent_eq_adelic_unipotent, unipAdele_eq, mul_assoc, ← realEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul, hZ _ hxZ]`. Rewrite using `[setIntegral_congr_fun (measurableSet_levelDomain 1) heq, setIntegral_levelDomain, levelConstant_one, one_smul]`.
-/
theorem wh_realEmb {φ : G2 → ℂ} (hL : LInv φ)
    (hZ : ∀ y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ, ∀ g, φ (g * finEmb ℚ 2 (unipFin y)) = φ g) (h : GL (Fin 2) ℝ) :
    Wh φ (realEmb h) = ∫ t in (0 : ℝ)..1, φ (realEmb (unipReal t * h)) *
      Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) := by
  have e1 : Wh φ (realEmb h) = ∫ x in levelDomain 1, φ (uni2 x * realEmb h) * (adelicChar ℚ (-x) : ℂ) ∂adeleMeasure ℚ :=
    (isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq (isAddFundamentalDomain_levelDomain 1)
      (wh_integrand_vadd hL _)
  rw [e1]
  set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h)) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) with hG
  have heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (uni2 x * realEmb h) * (adelicChar ℚ (-x) : ℂ))
      (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain 1) := by
    intro x hx
    have hxZ : x.2 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := levelIdeal_subset 1 hx.2
    simp only [hG]
    rw [adelicChar_neg_of_integral hxZ, unipotent_eq_adelic_unipotent, unipAdele_eq, mul_assoc,
      ← realEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul, hZ _ hxZ]
  rw [setIntegral_congr_fun (measurableSet_levelDomain 1) heq, setIntegral_levelDomain, levelConstant_one, one_smul]

/- English proof (translation)
Use `split_ifs with hm`. Simplify using `[hm]`. Establish `hc : (2 * Real.pi * Complex.I * m : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, hm, Complex.I_ne_zero]`. Rewrite using `[integral_exp_mul_complex hc]`.

Establish `: Complex.exp (2 * Real.pi * Complex.I * m * ((1 : ℝ) : ℂ)) = 1`. Rewrite using `[show (2 * Real.pi * Complex.I * m * ((1 : ℝ) : ℂ) : ℂ) = m * (2 * Real.pi * Complex.I) by push_cast; ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem integral_exp_int (m : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * m * (x : ℝ)) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · simp [hm]
  · have hc : (2 * Real.pi * Complex.I * m : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, hm, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * Complex.I * m * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I * m * ((1 : ℝ) : ℂ) : ℂ) = m * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    rw [this]
    simp

/- English proof (translation)
Establish `hcont : ∀ n, Continuous fun x : ℝ => b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))` using `fun n => by fun_prop`. Establish `hnorm : ∀ n (x : ℝ), ‖b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))‖ = ‖b n‖` using `fun n x => by`. Rewrite using `[norm_mul, show (2 * Real.pi * Complex.I * (m n) * (x : ℝ) : ℂ) = ((2 * Real.pi * (m n) * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]`. Establish `hs` using `hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := fun n (x : ℝ) => b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))) (fun n => (hcont n).integrableOn_Ioc) (by`. Establish `: ∀ n, ∫ x in Set.Ioc (0 : ℝ) 1, ‖b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))‖ = ‖b n‖` using `fun n => by`.

Simplify using `only [hnorm]`. Simplify using the standard rewrite rules. Simplify `hb)` using `only [this]`. Rewrite using `[intervalIntegral.integral_of_le zero_le_one, ← hs.tsum_eq]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul, integral_exp_int]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem integral_tsum_exp (b : ℕ → ℂ) (hb : Summable fun n => ‖b n‖) (m : ℕ → ℤ) :
    ∫ x in (0 : ℝ)..1, ∑' n, b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ)) =
      ∑' n, if m n = 0 then b n else 0 := by
  have hcont : ∀ n, Continuous fun x : ℝ => b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ)) := fun n => by
    fun_prop
  have hnorm : ∀ n (x : ℝ), ‖b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))‖ = ‖b n‖ := fun n x => by
    rw [norm_mul, show (2 * Real.pi * Complex.I * (m n) * (x : ℝ) : ℂ) = ((2 * Real.pi * (m n) * x : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hs := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := fun n (x : ℝ) => b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ)))
    (fun n => (hcont n).integrableOn_Ioc)
    (by
      have : ∀ n, ∫ x in Set.Ioc (0 : ℝ) 1, ‖b n * Complex.exp (2 * Real.pi * Complex.I * (m n) * (x : ℝ))‖ = ‖b n‖ := fun n => by
        simp only [hnorm]
        simp
      simpa only [this] using hb)
  rw [intervalIntegral.integral_of_le zero_le_one, ← hs.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul, integral_exp_int]
  split_ifs <;> simp

/- English proof (translation)
Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Use `set b : ℕ → ℂ := fun n => a n * Complex.exp (-2 * Real.pi * n * y) with hbdef`. Establish `hb : Summable fun n => ‖b n‖`. Establish `h0` using `hexp ⟨y * Complex.I, by simpa using hy⟩`. Use `(summable_norm_iff.2 ?_)` and prove the remaining obligations.

Use `h0.summable.congr fun n => ?_` and prove the remaining obligations. Simplify using `only [hbdef]`. Use `congr 2`. Express the relevant statement in the definitionally equal form `2 * Real.pi * Complex.I * n * (y * Complex.I) = _`. Take the linear combination `(2 * Real.pi * n * y) * hI`.

Establish `e : ∀ x : ℝ, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) = ∑' n, b n * Complex.exp (2 * Real.pi * Complex.I * ((σ * n + 1 : ℤ) : ℂ) * (x : ℝ))` using `fun x => by`. Rewrite using `[← (hexp (z x)).tsum_eq, ← tsum_mul_right]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Simplify using `only [hbdef]`. Rewrite using `[mul_assoc (a n), mul_assoc (a n), ← Complex.exp_add, ← Complex.exp_add, hz]`.

Use `congr 2`. Use `push_cast`. Take the linear combination `(2 * Real.pi * n * y) * hI`. Simplify using `only [e]`. Use `integral_tsum_exp b hb (fun n => σ * n + 1)` as an intermediate fact.

Conclude with `this`.
-/
theorem form_fourier {f : UpperHalfPlane → ℂ} {a : ℕ → ℂ}
    (hexp : ∀ τ : UpperHalfPlane, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ))
    {y : ℝ} (hy : 0 < y) (σ : ℤ) (z : ℝ → UpperHalfPlane) (hz : ∀ x : ℝ, (z x : ℂ) = σ * x + y * Complex.I) :
    ∫ x in (0 : ℝ)..1, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) =
      ∑' n : ℕ, if σ * n + 1 = 0 then a n * Complex.exp (-2 * Real.pi * n * y) else 0 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set b : ℕ → ℂ := fun n => a n * Complex.exp (-2 * Real.pi * n * y) with hbdef
  have hb : Summable fun n => ‖b n‖ := by
    have h0 := hexp ⟨y * Complex.I, by simpa using hy⟩
    refine (summable_norm_iff.2 ?_)
    refine h0.summable.congr fun n => ?_
    simp only [hbdef]
    congr 2
    change 2 * Real.pi * Complex.I * n * (y * Complex.I) = _
    linear_combination (2 * Real.pi * n * y) * hI
  have e : ∀ x : ℝ, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) =
      ∑' n, b n * Complex.exp (2 * Real.pi * Complex.I * ((σ * n + 1 : ℤ) : ℂ) * (x : ℝ)) := fun x => by
    rw [← (hexp (z x)).tsum_eq, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    simp only [hbdef]
    rw [mul_assoc (a n), mul_assoc (a n), ← Complex.exp_add, ← Complex.exp_add, hz]
    congr 2
    push_cast
    linear_combination (2 * Real.pi * n * y) * hI
  simp only [e]
  have := integral_tsum_exp b hb (fun n => σ * n + 1)
  exact this

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => x) a b = _`. Rewrite using `[unipMatrix_apply]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp`.
-/
theorem coe_unipReal (x : ℝ) : (unipReal x : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := by
  refine Matrix.ext fun a b => ?_
  change unipMatrix (n := 2) (r := 1) (fun _ => x) a b = _
  rw [unipMatrix_apply]
  fin_cases a <;> fin_cases b <;> simp

/- English proof (translation)
Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => y) a b = _`. Rewrite using `[unipMatrix_apply]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp`.
-/
theorem coe_unipFin (y : 𝔸f) : (unipFin y : Matrix (Fin 2) (Fin 2) 𝔸f) = !![1, y; 0, 1] := by
  refine Matrix.ext fun a b => ?_
  change unipMatrix (n := 2) (r := 1) (fun _ => y) a b = _
  rw [unipMatrix_apply]
  fin_cases a <;> fin_cases b <;> simp

/- English proof (translation)
Use `⟨(AdelicGLn.mem_integralFiniteGL_iff ℚ 2).2 ⟨fun a b => ?_, fun a b => ?_⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [coe_unipFin] fin_cases a <;> fin_cases b <;> simp [hy, one_mem, zero_mem]`. Rewrite using `[unipFin, coe_unipGL_inv]`. Express the relevant statement in the definitionally equal form `unipMatrix (n := 2) (r := 1) (fun _ => -y) a b ∈ _`. Rewrite using `[unipMatrix_apply]`.

Use `split_ifs`. Conclude with `neg_mem hy`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Rewrite using `[coe_unipFin]`.

Simplify using `using zero_mem_levelIdeal N`.
-/
theorem unipFin_mem (N : ℕ) [NeZero N] {y : 𝔸f} (hy : y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    unipFin y ∈ Gamma0Level N := by
  refine ⟨(AdelicGLn.mem_integralFiniteGL_iff ℚ 2).2 ⟨fun a b => ?_, fun a b => ?_⟩, ?_⟩
  · rw [coe_unipFin]
    fin_cases a <;> fin_cases b <;> simp [hy, one_mem, zero_mem]
  · rw [unipFin, coe_unipGL_inv]
    change unipMatrix (n := 2) (r := 1) (fun _ => -y) a b ∈ _
    rw [unipMatrix_apply]
    split_ifs
    · exact neg_mem hy
    · exact one_mem _
    · exact zero_mem _
  · rw [coe_unipFin]
    simpa using zero_mem_levelIdeal N

section

variable {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}

/- English proof (translation)
Use `hl.level u hu 1 (fun v => by simp [lf]) (fun v _ => by simp [lf, hd v]) g` as an intermediate fact. Simplify using `using this`.
-/
theorem level_one (hl : Lift k N f ω φ) {u : AdelicGLn.FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N)
    (hd : ∀ v : Pl, glAt v u 1 1 = 1) (g : G2) : φ (g * finEmb ℚ 2 u) = φ g := by
  have := hl.level u hu 1 (fun v => by simp [lf]) (fun v _ => by simp [lf, hd v]) g
  simpa using this

/- English proof (translation)
Establish `h1` using `hl.left epsilon (realEmb M)`. Rewrite using `[← h1]`. Establish `h2 : (dia2 epsilon : G2) * realEmb M = realEmb (toReal epsilon * M) * finEmb ℚ 2 (AdelicGLn.finiteDiagonal ℚ 2 epsilon)`. Express the relevant statement in the definitionally equal form `AdelicGLn.diagonal ℚ 2 epsilon * realEmb M = _`. Rewrite using `[diagonal_eq]`.

Apply `(AdelicGLn.prodEquiv ℚ 2).injective` to reduce the goal to its premises. Simplify using `only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]`. Rewrite using `[h2]`. Use `level_one hl (finiteDiagonal_epsilon_mem N) (fun v => ?_) _` and prove the remaining obligations. Rewrite using `[GodementSection.glAt_apply, AdelicGLn.finiteDiagonal_apply]`.

Simplify using `[epsilon]`. Both sides reduce to the same expression.
-/
theorem real_neg (hl : Lift k N f ω φ) (M : GL (Fin 2) ℝ) :
    φ (realEmb M) = φ (realEmb (toReal epsilon * M)) := by
  have h1 := hl.left epsilon (realEmb M)
  rw [← h1]
  have h2 : (dia2 epsilon : G2) * realEmb M =
      realEmb (toReal epsilon * M) * finEmb ℚ 2 (AdelicGLn.finiteDiagonal ℚ 2 epsilon) := by
    change AdelicGLn.diagonal ℚ 2 epsilon * realEmb M = _
    rw [diagonal_eq]
    apply (AdelicGLn.prodEquiv ℚ 2).injective
    simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  rw [h2]
  refine level_one hl (finiteDiagonal_epsilon_mem N) (fun v => ?_) _
  rw [GodementSection.glAt_apply, AdelicGLn.finiteDiagonal_apply]
  simp [epsilon]
  rfl

/- English proof (translation)
Establish `e : M = borelGL z` using `Units.ext (by rw [hM, coe_borelGL, hz1, hz2])`. Rewrite using `[e, hl.real _ (det_borelGL_pos z), archLift_borelGL, hz2]`.
-/
theorem real_pos (hl : Lift k N f ω φ) (x t : ℝ) (ht : 0 < t) (z : UpperHalfPlane) (hz1 : z.re = x) (hz2 : z.im = t)
    (M : GL (Fin 2) ℝ) (hM : (M : Matrix (Fin 2) (Fin 2) ℝ) = !![t, x; 0, 1]) :
    φ (realEmb M) = (Real.sqrt t : ℂ) ^ (k : ℤ) * f z := by
  have e : M = borelGL z := Units.ext (by rw [hM, coe_borelGL, hz1, hz2])
  rw [e, hl.real _ (det_borelGL_pos z), archLift_borelGL, hz2]

/- English proof (translation)
Use `level_one hl (unipFin_mem N hy) (fun v => ?_) g` and prove the remaining obligations. Rewrite using `[GodementSection.glAt_apply, coe_unipFin]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem hZ_of_lift (hl : Lift k N f ω φ) (y : 𝔸f) (hy : y ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (g : G2) :
    φ (g * finEmb ℚ 2 (unipFin y)) = φ g := by
  refine level_one hl (unipFin_mem N hy) (fun v => ?_) g
  rw [GodementSection.glAt_apply, coe_unipFin]
  simp
  rfl

end

/- English proof (translation)
Rewrite using `[WR, if_neg (not_lt.2 ht.le)]`.
-/
theorem wr_pos (k : ℕ) (t : ℝˣ) (ht : 0 < (t : ℝ)) : WR k t = 0 := by
  rw [WR, if_neg (not_lt.2 ht.le)]

/- English proof (translation)
Rewrite using `[wh_realEmb hl.left (hZ_of_lift hl)]`. Break down `lt_or_gt_of_ne t.ne_zero with ht | ht` into its components or cases. Establish `hy : 0 < -(t : ℝ)` using `neg_pos.2 ht`. Set `z : ℝ → UpperHalfPlane` to `fun x => ⟨⟨-x, -(t : ℝ)⟩, hy⟩`. Establish `hv : ∀ x : ℝ, φ (realEmb (unipReal x * dg2 t 1)) = (Real.sqrt (-(t : ℝ)) : ℂ) ^ (k : ℤ) * f (z x)` using `fun x => by`.

Rewrite using `[real_neg hl]`. Use `real_pos hl (-x) (-(t : ℝ)) hy (z x) rfl rfl _ ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, coe_unipReal]`. Establish `he : ((toReal epsilon : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[toReal_apply]`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [epsilon]`. Rewrite using `[he]`. Simplify using `[dg2, Matrix.mul_fin_two]`. Establish `e : ∫ x in (0 : ℝ)..1, φ (realEmb (unipReal x * dg2 t 1)) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) = (Real.sqrt (-(t : ℝ)) : ℂ) ^ (k : ℤ) * ∫ x in (0 : ℝ)..1, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ))`.

Rewrite using `[← intervalIntegral.integral_const_mul]`. Use `intervalIntegral.integral_congr fun x _ => ?_` and prove the remaining obligations. Simplify using `only [hv, mul_assoc]`. Establish `hz : ∀ x : ℝ, (z x : ℂ) = ((-1 : ℤ) : ℂ) * x + ((-(t : ℝ) : ℝ) : ℂ) * Complex.I` using `fun x => by`. Apply the tactic sequence `apply Complex.ext <;> simp [z]`.

Rewrite using `[e, form_fourier hexp hy (-1) z hz]`. Establish `hs : (∑' n : ℕ, if (-1 : ℤ) * n + 1 = 0 then a n * Complex.exp (-2 * Real.pi * n * ((-(t : ℝ) : ℝ) : ℂ)) else 0) = Complex.exp (-2 * Real.pi * ((-(t : ℝ) : ℝ) : ℂ))`. Rewrite using `[tsum_eq_single 1 (fun n hn => if_neg (by omega))]`. Simplify using `[h1]`. Rewrite using `[hs, WR, if_pos ht, abs_of_neg ht]`.

Use `push_cast`. Rewrite using `[zpow_natCast]`. Establish `hy : 0 < (t : ℝ)` using `ht`. Set `z : ℝ → UpperHalfPlane` to `fun x => ⟨⟨x, (t : ℝ)⟩, hy⟩`. Establish `hv : ∀ x : ℝ, φ (realEmb (unipReal x * dg2 t 1)) = (Real.sqrt (t : ℝ) : ℂ) ^ (k : ℤ) * f (z x)` using `fun x => by`.

Use `real_pos hl x (t : ℝ) hy (z x) rfl rfl _ ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, coe_unipReal]`. Simplify using `[dg2, Matrix.mul_fin_two]`. Establish `e : ∫ x in (0 : ℝ)..1, φ (realEmb (unipReal x * dg2 t 1)) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) = (Real.sqrt (t : ℝ) : ℂ) ^ (k : ℤ) * ∫ x in (0 : ℝ)..1, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ))`. Rewrite using `[← intervalIntegral.integral_const_mul]`.

Use `intervalIntegral.integral_congr fun x _ => ?_` and prove the remaining obligations. Simplify using `only [hv, mul_assoc]`. Establish `hz : ∀ x : ℝ, (z x : ℂ) = ((1 : ℤ) : ℂ) * x + ((t : ℝ) : ℂ) * Complex.I` using `fun x => by`. Apply the tactic sequence `apply Complex.ext <;> simp [z]`. Rewrite using `[e, form_fourier hexp hy 1 z hz, wr_pos k t hy]`.

Establish `hn : ∀ n : ℕ, ¬ ((1 : ℤ) * n + 1 = 0)` using `fun n => by omega`. Rewrite using `[tsum_congr (fun n => if_neg (hn n)), tsum_zero, mul_zero]`.
-/
theorem whittaker_value {k N : ℕ} [NeZero N] {f : UpperHalfPlane → ℂ} {a : ℕ → ℂ} {ω : HeckeCharacter ℚ} {φ : G2 → ℂ}
    (hexp : ∀ τ : UpperHalfPlane, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ))
    (h1 : a 1 = 1) (hl : Lift k N f ω φ) (t : ℝˣ) : Wh φ (realEmb (dg2 t 1)) = WR k t := by
  rw [wh_realEmb hl.left (hZ_of_lift hl)]
  rcases lt_or_gt_of_ne t.ne_zero with ht | ht
  · have hy : 0 < -(t : ℝ) := neg_pos.2 ht
    let z : ℝ → UpperHalfPlane := fun x => ⟨⟨-x, -(t : ℝ)⟩, hy⟩
    have hv : ∀ x : ℝ, φ (realEmb (unipReal x * dg2 t 1)) = (Real.sqrt (-(t : ℝ)) : ℂ) ^ (k : ℤ) * f (z x) := fun x => by
      rw [real_neg hl]
      refine real_pos hl (-x) (-(t : ℝ)) hy (z x) rfl rfl _ ?_
      rw [Units.val_mul, Units.val_mul, coe_unipReal]
      have he : ((toReal epsilon : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, 0; 0, 1] := by
        refine Matrix.ext fun a b => ?_
        rw [toReal_apply]
        fin_cases a <;> fin_cases b <;> simp [epsilon]
      rw [he]
      simp [dg2, Matrix.mul_fin_two]
    have e : ∫ x in (0 : ℝ)..1, φ (realEmb (unipReal x * dg2 t 1)) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) =
        (Real.sqrt (-(t : ℝ)) : ℂ) ^ (k : ℤ) * ∫ x in (0 : ℝ)..1, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hv, mul_assoc]
    have hz : ∀ x : ℝ, (z x : ℂ) = ((-1 : ℤ) : ℂ) * x + ((-(t : ℝ) : ℝ) : ℂ) * Complex.I := fun x => by
      apply Complex.ext <;> simp [z]
    rw [e, form_fourier hexp hy (-1) z hz]
    have hs : (∑' n : ℕ, if (-1 : ℤ) * n + 1 = 0 then a n * Complex.exp (-2 * Real.pi * n * ((-(t : ℝ) : ℝ) : ℂ)) else 0) =
        Complex.exp (-2 * Real.pi * ((-(t : ℝ) : ℝ) : ℂ)) := by
      rw [tsum_eq_single 1 (fun n hn => if_neg (by omega))]
      simp [h1]
    rw [hs, WR, if_pos ht, abs_of_neg ht]
    push_cast
    rw [zpow_natCast]
  · have hy : 0 < (t : ℝ) := ht
    let z : ℝ → UpperHalfPlane := fun x => ⟨⟨x, (t : ℝ)⟩, hy⟩
    have hv : ∀ x : ℝ, φ (realEmb (unipReal x * dg2 t 1)) = (Real.sqrt (t : ℝ) : ℂ) ^ (k : ℤ) * f (z x) := fun x => by
      refine real_pos hl x (t : ℝ) hy (z x) rfl rfl _ ?_
      rw [Units.val_mul, coe_unipReal]
      simp [dg2, Matrix.mul_fin_two]
    have e : ∫ x in (0 : ℝ)..1, φ (realEmb (unipReal x * dg2 t 1)) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) =
        (Real.sqrt (t : ℝ) : ℂ) ^ (k : ℤ) * ∫ x in (0 : ℝ)..1, f (z x) * Complex.exp (2 * Real.pi * Complex.I * (x : ℝ)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hv, mul_assoc]
    have hz : ∀ x : ℝ, (z x : ℂ) = ((1 : ℤ) : ℂ) * x + ((t : ℝ) : ℂ) * Complex.I := fun x => by
      apply Complex.ext <;> simp [z]
    rw [e, form_fourier hexp hy 1 z hz, wr_pos k t hy]
    have hn : ∀ n : ℕ, ¬ ((1 : ℤ) * n + 1 = 0) := fun n => by omega
    rw [tsum_congr (fun n => if_neg (hn n)), tsum_zero, mul_zero]

/- English proof (translation)
Introduce `k N _ _ χ _ f a hf ha ω φ _ hl`. Conclude with `⟨wh_continuous hl.cont, fun x g => wh_law hl.left x g, fun z g => wh_central hl.cen z g, fun t => whittaker_value hf.exp ha.2.1 hl t⟩`.
-/
theorem whittaker_of_lift : Ad3.R.F2 := by
  intro k N _ _ χ _ f a hf ha ω φ _ hl
  exact ⟨wh_continuous hl.cont, fun x g => wh_law hl.left x g, fun z g => wh_central hl.cen z g,
    fun t => whittaker_value hf.exp ha.2.1 hl t⟩

end GlobalTheory.CompanionTheory.RsWhittaker

end
