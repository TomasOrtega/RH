import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsBasic
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsSchur

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

def fY (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (e : V) (p : G × G) : HH :=
  ⟪W (p.2⁻¹ * p.1), e⟫_ℂ • σ (p.2⁻¹ * p.1) w

/- English proof (translation)
Establish `hc : Continuous (fun p : G × G => p.2⁻¹ * p.1)` using `continuous_snd.inv.mul continuous_fst`. Establish `h1 : Continuous (fun p : G × G => W (p.2⁻¹ * p.1))` using `hW.comp hc`. Establish `h2 : Continuous (fun p : G × G => σ (p.2⁻¹ * p.1) w)` using `(hσ.2.2.2 w).comp hc`. Conclude with `(h1.inner continuous_const).smul h2`.
-/
theorem continuous_fY {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hW : Continuous W)
    (e : V) : Continuous (fY σ w W e) := by
  have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1) := continuous_snd.inv.mul continuous_fst
  have h1 : Continuous (fun p : G × G => W (p.2⁻¹ * p.1)) := hW.comp hc
  have h2 : Continuous (fun p : G × G => σ (p.2⁻¹ * p.1) w) := (hσ.2.2.2 w).comp hc
  exact (h1.inner continuous_const).smul h2

/- English proof (translation)
Establish `h` using `hσ.2.2.1 x a a`. Establish `h2 : ‖σ x a‖ ^ 2 = ‖a‖ ^ 2`. Rewrite using `[@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, h]`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (σ x a)), h2, Real.sqrt_sq (norm_nonneg a)]`.
-/
private theorem norm_rep_apply_of_isUnitRep {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (x : G) (a : HH) :
    ‖σ x a‖ = ‖a‖ := by
  have h := hσ.2.2.1 x a a
  have h2 : ‖σ x a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, h]
  rw [← Real.sqrt_sq (norm_nonneg (σ x a)), h2, Real.sqrt_sq (norm_nonneg a)]

/- English proof (translation)
Unfold `fY`. Rewrite using `[norm_smul, norm_rep_apply_of_isUnitRep hσ]`. Conclude with `mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)`.
-/
theorem norm_fY_le {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) (W : G → V) (e : V) (p : G × G) :
    ‖fY σ w W e p‖ ≤ ‖W (p.2⁻¹ * p.1)‖ * ‖e‖ * ‖w‖ := by
  unfold fY
  rw [norm_smul, norm_rep_apply_of_isUnitRep hσ]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)

/- English proof (translation)
Rewrite using `[ae_iff]`. Establish `hs : {p : G × G | ¬ p.2 ∈ A} = (Set.univ : Set G) ×ˢ Aᶜ`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[hs, Measure.prod_prod, Measure.restrict_apply hA.compl, Set.compl_inter_self, measure_empty, mul_zero]`.
-/
private theorem ae_prod_restrict_snd_mem {ν μS : Measure G} [SFinite ν] [SFinite μS] {A : Set G} (hA : MeasurableSet A) :
    ∀ᵐ p ∂(ν.prod (μS.restrict A)), p.2 ∈ A := by
  rw [ae_iff]
  have hs : {p : G × G | ¬ p.2 ∈ A} = (Set.univ : Set G) ×ˢ Aᶜ := by
    ext p
    simp
  rw [hs, Measure.prod_prod, Measure.restrict_apply hA.compl, Set.compl_inter_self, measure_empty,
    mul_zero]

/- English proof (translation)
Establish `: IsFiniteMeasure (μS.restrict A)` using `⟨by rwa [Measure.restrict_apply_univ]⟩`. Establish `hWc : Continuous W` using `hW.2.2.2.2.1`. Establish `hWi : Integrable (fun z => ‖W z‖) ν`. Use `⟨hWc.norm.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Simplify `hW.2.2.2.2.2.2.1` using `[HasFiniteIntegral, enorm_norm]`.

Establish `hg : Integrable (fun p : G × G => ‖W p.1‖ * (‖e‖ * ‖w‖)) (ν.prod (μS.restrict A))` using `hWi.mul_prod (integrable_const (‖e‖ * ‖w‖))`. Use `hg.mono' (continuous_fY hσ w hWc e).aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards [ae_prod_restrict_snd_mem (ν := ν) (μS := μS) hA] with p hp`. Establish `h1` using `norm_fY_le hσ w W e p`. Rewrite `h1` using `[(norm_W_shift hW) hinv (hAS hp)]`.

Conclude with `h1.trans_eq (by ring)`.
-/
theorem integrable_fY {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : Integrable (fY σ w W e) (ν.prod (μS.restrict A)) := by
  have : IsFiniteMeasure (μS.restrict A) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hWc : Continuous W := hW.2.2.2.2.1
  have hWi : Integrable (fun z => ‖W z‖) ν := by
    refine ⟨hWc.norm.aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_norm] using hW.2.2.2.2.2.2.1
  have hg : Integrable (fun p : G × G => ‖W p.1‖ * (‖e‖ * ‖w‖)) (ν.prod (μS.restrict A)) :=
    hWi.mul_prod (integrable_const (‖e‖ * ‖w‖))
  refine hg.mono' (continuous_fY hσ w hWc e).aestronglyMeasurable ?_
  filter_upwards [ae_prod_restrict_snd_mem (ν := ν) (μS := μS) hA] with p hp
  have h1 := norm_fY_le hσ w W e p
  rw [(norm_W_shift hW) hinv (hAS hp)] at h1
  exact h1.trans_eq (by ring)

/- English proof (translation)
Rewrite using `[integral_prod _ (integrable_fY hσ hW hinv hA hAS hAf e)]`. Both sides reduce to the same expression.
-/
theorem yv_eq_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν : Measure G} [SFinite ν]
    [SFinite μS] {d : ℝ} {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) {A : Set G} (hA : MeasurableSet A) (hAS : A ⊆ S)
    (hAf : μS A < ⊤) (e : V) : yv μS ν σ w W A e = ∫ p, fY σ w W e p ∂(ν.prod (μS.restrict A)) := by
  rw [integral_prod _ (integrable_fY hσ hW hinv hA hAS hAf e)]
  rfl

/- English proof (translation)
Establish `h : ∫ x, ⟪v, f x⟫_ℂ ∂m = ⟪v, ∫ x, f x ∂m⟫_ℂ` using `integral_inner hf v`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inner_integral_left {α : Type*} [MeasurableSpace α] {m : Measure α} {f : α → HH} (hf : Integrable f m)
    (v : HH) : ⟪∫ x, f x ∂m, v⟫_ℂ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by
  have h : ∫ x, ⟪v, f x⟫_ℂ ∂m = ⟪v, ∫ x, f x ∂m⟫_ℂ := integral_inner hf v
  calc ⟪∫ x, f x ∂m, v⟫_ℂ = conj ⟪v, ∫ x, f x ∂m⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∫ x, ⟪v, f x⟫_ℂ ∂m) := by rw [h]
    _ = ∫ x, conj ⟪v, f x⟫_ℂ ∂m := integral_conj.symm
    _ = ∫ x, ⟪f x, v⟫_ℂ ∂m := by simp_rw [inner_conj_symm]

def Xop (μS ν μS' ν' : Measure G) (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V')
    (A A' : Set G) (γ : G) : V' →L[ℂ] V :=
  (d : ℂ) • sand σ (Yop μS ν σ w W A) (Yop μS' ν' σ w W' A') γ

/- English proof (translation)
Establish `hcol : ∀ j, X (stdOrthonormalBasis ℂ V' j) = Z (stdOrthonormalBasis ℂ V' j)`. Introduce `j`. Use `first`. Consider the case `exact ext_inner_left_basis (stdOrthonormalBasis ℂ V).toBasis (fun i => by simpa using h i j)`. Consider the case `(apply (stdOrthonormalBasis ℂ V).repr.injective`.

Use extensionality with `i`. Simplify `h i j)` using `[OrthonormalBasis.repr_apply_apply]`. Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Conclude with `(stdOrthonormalBasis ℂ V').toBasis.ext (fun j => by simpa using hcol j)`.
-/
theorem op_ext_basis (X Z : V' →L[ℂ] V)
    (h : ∀ i j, ⟪stdOrthonormalBasis ℂ V i, X (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ⟪stdOrthonormalBasis ℂ V i, Z (stdOrthonormalBasis ℂ V' j)⟫_ℂ) : X = Z := by
  have hcol : ∀ j, X (stdOrthonormalBasis ℂ V' j) = Z (stdOrthonormalBasis ℂ V' j) := by
    intro j
    first
    | exact ext_inner_left_basis (stdOrthonormalBasis ℂ V).toBasis (fun i => by simpa using h i j)
    | (apply (stdOrthonormalBasis ℂ V).repr.injective
       ext i
       simpa [OrthonormalBasis.repr_apply_apply] using h i j)
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ V').toBasis.ext (fun j => by simpa using hcol j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem rk1A_apply (u : V) (v : V') (x : V') : Formalism.L2.SG.Pf.EnergyAbs.rk1A u v x = ⟪v, x⟫_ℂ • u := by
  rfl

/- English proof (translation)
Unfold `kG fY φinv`. Simplify using `only [ContinuousLinearMap.smul_apply, rk1A_apply, inner_smul_right, inner_smul_left, map_smul, inner_conj_symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem inner_kG_apply_eq (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V')
    (γ : G) (a : V) (b : V') (p p' : G × G) :
    ⟪a, kG σ d w W W' γ (φinv p, φinv p') b⟫_ℂ =
      (d : ℂ) * ⟪fY σ w W a p, σ γ (fY σ w W' b p')⟫_ℂ := by
  unfold kG fY φinv
  simp only [ContinuousLinearMap.smul_apply, rk1A_apply, inner_smul_right, inner_smul_left,
    map_smul, inner_conj_symm]
  ring

/- English proof (translation)
Conclude with `hF.apply_continuousLinearMap b`.
-/
private theorem integrable_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (b : V') : Integrable (fun x => F x b) m := by
  exact hF.apply_continuousLinearMap b

/- English proof (translation)
Conclude with `(integrable_apply_of_integrable_clm hF b).const_inner a`.
-/
private theorem integrable_inner_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : Integrable (fun x => ⟪a, F x b⟫_ℂ) m := by
  exact (integrable_apply_of_integrable_clm hF b).const_inner a

/- English proof (translation)
Establish `happ : (∫ x, F x ∂m) b = ∫ x, F x b ∂m`. Conclude with `ContinuousLinearMap.integral_apply hF b`. Rewrite using `[happ]`. Conclude with `(integral_inner (integrable_apply_of_integrable_clm hF b) a).symm`.
-/
private theorem inner_integral_clm_apply_eq_integral {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : ⟪a, (∫ x, F x ∂m) b⟫_ℂ = ∫ x, ⟪a, F x b⟫_ℂ ∂m := by
  have happ : (∫ x, F x ∂m) b = ∫ x, F x b ∂m := by
    exact ContinuousLinearMap.integral_apply hF b
  rw [happ]
  exact (integral_inner (integrable_apply_of_integrable_clm hF b) a).symm

/- English proof (translation)
Use `op_ext_basis _ _ (fun i j => ?_)` and prove the remaining obligations. Establish `hf` using `integrable_fY hσ hW hinv hA hAS hAf (stdOrthonormalBasis ℂ V i)`. Establish `hf'` using `integrable_fY hσ hW' hinv' hA' hAS' hAf' (stdOrthonormalBasis ℂ V' j)`. Establish `hL : ⟪stdOrthonormalBasis ℂ V i, Xop μS ν μS' ν' σ d w W W' A A' γ (stdOrthonormalBasis ℂ V' j)⟫_ℂ = ∫ p, ∫ p', (d : ℂ) * ⟪fY σ w W (stdOrthonormalBasis ℂ V i) p, σ γ (fY σ w W' (stdOrthonormalBasis ℂ V' j) p')⟫_ℂ ∂(ν'.prod (μS'.restrict A')) ∂(ν.prod (μS.restrict A))`. Rewrite using `[Xop, ContinuousLinearMap.smul_apply, inner_smul_right, inner_sand, Yop_apply_basis, Yop_apply_basis, yv_eq_integral hσ hW hinv hA hAS hAf, yv_eq_integral hσ hW' hinv' hA' hAS' hAf', ← (σ γ).integral_comp_comm hf', inner_integral_left hf, ← integral_const_mul]`.

Use `integral_congr_ae (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[integral_const_mul, integral_inner ((σ γ).integrable_comp hf')]`. Rewrite using `[hL, inner_integral_clm_apply_eq_integral hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j), integral_prod _ (integrable_inner_apply_of_integrable_clm hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j))]`. Use `integral_congr_ae (ae_of_all _ fun p => ?_)` and prove the remaining obligations.

Apply the tactic sequence `try dsimp only`. Use `integral_congr_ae (ae_of_all _ fun p' => ?_)` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Conclude with `(inner_kG_apply_eq σ d w W W' γ _ _ p p').symm`.
-/
theorem Xop_eq_integral {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite μS] [SFinite ν'] [SFinite μS'] {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') {A A' : Set G} (hA : MeasurableSet A)
    (hAS : A ⊆ S) (hAf : μS A < ⊤) (hA' : MeasurableSet A') (hAS' : A' ⊆ S') (hAf' : μS' A' < ⊤) (γ : G)
    (hK : Integrable (fun q : (G × G) × (G × G) => kG σ d w W W' γ (φinv q.1, φinv q.2))
      ((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')))) :
    Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q, kG σ d w W W' γ (φinv q.1, φinv q.2) ∂((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A'))) := by
  refine op_ext_basis _ _ (fun i j => ?_)
  have hf := integrable_fY hσ hW hinv hA hAS hAf (stdOrthonormalBasis ℂ V i)
  have hf' := integrable_fY hσ hW' hinv' hA' hAS' hAf' (stdOrthonormalBasis ℂ V' j)
  have hL : ⟪stdOrthonormalBasis ℂ V i,
      Xop μS ν μS' ν' σ d w W W' A A' γ (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ∫ p, ∫ p', (d : ℂ) * ⟪fY σ w W (stdOrthonormalBasis ℂ V i) p,
        σ γ (fY σ w W' (stdOrthonormalBasis ℂ V' j) p')⟫_ℂ
          ∂(ν'.prod (μS'.restrict A')) ∂(ν.prod (μS.restrict A)) := by
    rw [Xop, ContinuousLinearMap.smul_apply, inner_smul_right, inner_sand,
      Yop_apply_basis, Yop_apply_basis,
      yv_eq_integral hσ hW hinv hA hAS hAf,
      yv_eq_integral hσ hW' hinv' hA' hAS' hAf',
      ← (σ γ).integral_comp_comm hf', inner_integral_left hf, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    try dsimp only
    rw [integral_const_mul, integral_inner ((σ γ).integrable_comp hf')]
  rw [hL, inner_integral_clm_apply_eq_integral hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j),
    integral_prod _ (integrable_inner_apply_of_integrable_clm hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  try dsimp only
  refine integral_congr_ae (ae_of_all _ fun p' => ?_)
  try dsimp only
  exact (inner_kG_apply_eq σ d w W W' γ _ _ p p').symm

end Formalism.L2.S.Pv.EnergyAbs
