import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.EnergyCut

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Use `set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) with hb`. Use `set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) => X.tensU u' (fun v => b v (i v)) with he`. Establish `hon : Orthonormal ℂ e`. Rewrite using `[orthonormal_iff_ite]`. Introduce `i j`.

Simplify using `only [he, X.tensU_inner]`. Establish `hloc : ∀ v, ⟪b v (i v), b v (j v)⟫_ℂ = if i v = j v then 1 else 0` using `fun v => (orthonormal_iff_ite.1 (b v).orthonormal) (i v) (j v)`. Simplify using `only [hloc]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Take `⟨v, hv⟩` from `Function.ne_iff.1 hij`. Rewrite using `[if_neg hij]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)`. Use `⟨hon, ?_⟩` and prove the remaining obligations.

Establish `hmem : ∀ x, X.tensU u' x ∈ Submodule.span ℂ (Set.range e)`. Introduce `x`. Establish `hp : X.tensU u' x = ∑ i, ⟪e i, X.tensU u' x⟫_ℂ • e i`. Apply `Formalism.L2.SG.RealObj.RankOneTensors.eq_of_inner_tens (X.tensU u') (X.tensU_span u')` to reduce the goal to its premises. Introduce `z`.

Rewrite using `[inner_sum, show ⟪X.tensU u' z, X.tensU u' x⟫_ℂ = ∏ v, ⟪z v, x v⟫_ℂ from X.tensU_inner u' z x]`. Establish `hterm : ∀ i, ⟪X.tensU u' z, ⟪e i, X.tensU u' x⟫_ℂ • e i⟫_ℂ = ∏ v, (⟪z v, b v (i v)⟫_ℂ * ⟪b v (i v), x v⟫_ℂ)`. Introduce `i`. Rewrite using `[inner_smul_right]`. Simplify using `only [he, X.tensU_inner]`.

Rewrite using `[Finset.prod_mul_distrib, mul_comm]`. Simplify using `only [hterm]`. Rewrite using `[← Fintype.prod_sum (fun v j => ⟪z v, b v j⟫_ℂ * ⟪b v j, x v⟫_ℂ)]`. Conclude with `Finset.prod_congr rfl fun v _ => ((b v).sum_inner_mul_inner (z v) (x v)).symm`. Rewrite using `[hp]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[← X.tensU_span u', Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hmem x`.
-/
theorem tens_onb (u' : D.what₂.Word) :
    Orthonormal ℂ (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v))) ∧
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)))) := by
  set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) with hb
  set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) => X.tensU u' (fun v => b v (i v)) with he
  have hon : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [he, X.tensU_inner]
    have hloc : ∀ v, ⟪b v (i v), b v (j v)⟫_ℂ = if i v = j v then 1 else 0 := fun v =>
      (orthonormal_iff_ite.1 (b v).orthonormal) (i v) (j v)
    simp only [hloc]
    by_cases hij : i = j
    · subst hij; simp
    · obtain ⟨v, hv⟩ := Function.ne_iff.1 hij
      rw [if_neg hij]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  refine ⟨hon, ?_⟩
  have hmem : ∀ x, X.tensU u' x ∈ Submodule.span ℂ (Set.range e) := by
    intro x
    have hp : X.tensU u' x = ∑ i, ⟪e i, X.tensU u' x⟫_ℂ • e i := by
      apply Formalism.L2.SG.RealObj.RankOneTensors.eq_of_inner_tens (X.tensU u') (X.tensU_span u')
      intro z
      rw [inner_sum, show ⟪X.tensU u' z, X.tensU u' x⟫_ℂ = ∏ v, ⟪z v, x v⟫_ℂ from X.tensU_inner u' z x]
      have hterm : ∀ i, ⟪X.tensU u' z, ⟪e i, X.tensU u' x⟫_ℂ • e i⟫_ℂ =
          ∏ v, (⟪z v, b v (i v)⟫_ℂ * ⟪b v (i v), x v⟫_ℂ) := by
        intro i
        rw [inner_smul_right]
        simp only [he, X.tensU_inner]
        rw [Finset.prod_mul_distrib, mul_comm]
      simp only [hterm]
      rw [← Fintype.prod_sum (fun v j => ⟪z v, b v j⟫_ℂ * ⟪b v j, x v⟫_ℂ)]
      exact Finset.prod_congr rfl fun v _ => ((b v).sum_inner_mul_inner (z v) (x v)).symm
    rw [hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← X.tensU_span u', Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hmem x

/- English proof (translation)
Take `⟨hon, hsp⟩` from `tens_onb X u'`. Set `B` to `OrthonormalBasis.mk hon hsp`. Establish `hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v))` using `fun i => by`. Simplify using `[B]`. Establish `hF` using `Formalism.L2.SG.RealObj.RankOneTensors.OOFactor_holds X u u' γ`.

Unfold `hs2`. Rewrite using `[Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]`. Simplify using `only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]`. Rewrite using `[Fintype.prod_sum]`.
-/
theorem hilbert_schmidt_tensor_product_factor (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    hs2 (OOinf X u u' γ) = ∏ v, hs2 (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
      Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  obtain ⟨hon, hsp⟩ := tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by
    simp [B]
  have hF := Formalism.L2.SG.RealObj.RankOneTensors.OOFactor_holds X u u' γ
  unfold hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GoodV (u u' : D.what₂.Word) : Set (Fin (D.R.rS + 1) → ℂ) :=
  {cv | (∀ l, cv l ≠ 0) ∧ 0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)}

def wtV (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ) : ℝ :=
  Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv) ^ (D.R.k - 1) * JacV (Matrix.diagonal cv)

def dcV : Measure (Fin (D.R.rS + 1) → ℂ) := Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def JvX (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Vloc u' v →L[ℂ] X.Vloc u v :=
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g

def LocEnergy (u u' : D.what₂.Word) (sc : ℝ) : Prop :=
  ∃ (Cv a a' : InfinitePlace X.B.I.F → ℝ) (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ),
    (∀ v, 0 ≤ Cv v ∧ 0 ≤ a v ∧ 0 ≤ a' v ∧ Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    DisintegrationConstant X u u' sc = ∏ v, Cv v ∧ (∏ v, a v * a' v) ≤ 1 ∧
    (∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' sc c) v)) = L v (c v)) ∧
    ∀ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (Cv v * wtV u u' cv * L v cv) ∂(dcV (D := D)) ≤
      ENNReal.ofReal (a v * a' v / X.dv v)

/- English proof (translation)
Simplify using `only [Gv, Dl, le_refl, Nat.le_succ, ↓reduceDIte]`. Use `fun_prop`.
-/
theorem gv_diag_cont (u u' : D.what₂.Word) :
    Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)) := by
  simp only [Gv, Dl, le_refl, Nat.le_succ, ↓reduceDIte]
  fun_prop

/- English proof (translation)
Establish `h1 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ | ∀ l, cv l ≠ 0}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`. Establish `h2 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ | 0 < Gv (Tw (D` using `D) u) (Tw (D := D) u') (Matrix.diagonal cv)} := isOpen_lt continuous_const (gv_diag_cont u u')`. Conclude with `(h1.inter h2).measurableSet`.
-/
theorem goodV_meas (u u' : D.what₂.Word) : MeasurableSet (GoodV u u') := by
  have h1 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ | ∀ l, cv l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ |
      0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)} :=
    isOpen_lt continuous_const (gv_diag_cont u u')
  exact (h1.inter h2).measurableSet

/- English proof (translation)
Use extensionality with `c`. Simplify using `[Good, GoodV, Set.mem_pi]`.
-/
theorem good_eq_pi (u u' : D.what₂.Word) : Good X u u' = Set.pi Set.univ (fun _ => GoodV u u') := by
  ext c
  simp [Good, GoodV, Set.mem_pi]

/- English proof (translation)
Unfold `wtV JacV`. Conclude with `mul_nonneg (pow_nonneg h.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)`.
-/
theorem wtV_nonneg (u u' : D.what₂.Word) {cv : Fin (D.R.rS + 1) → ℂ} (h : cv ∈ GoodV u u') :
    0 ≤ wtV u u' cv := by
  unfold wtV JacV
  exact mul_nonneg (pow_nonneg h.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`.

Repeatedly rewrite using `[Fin.succAbove_zero, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero]`. Simplify using `[Fin.succAbove_zero]`. Use `_ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by`. Rewrite using `[← ih (fun i => f (Fin.succ i)) (fun i => hf _)]`. Conclude with `lintegral_prod_mul (hf 0).aemeasurable (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable`.

Use `_ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]`.
-/
private theorem lintegral_pi_fin_prod_eq_prod_lintegral {n : ℕ} {E : Type*} [MeasurableSpace E]
    {μ : Fin n → Measure E} [∀ i, SigmaFinite (μ i)] (f : Fin n → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x : Fin (n + 1) → E, ∏ i, f i (x i) ∂(Measure.pi μ)
        = ∫⁻ x : E × (Fin n → E), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ (Fin.succ i))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [Fin.succAbove_zero, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero]
          simp [Fin.succAbove_zero]
      _ = (∫⁻ x, f 0 x ∂(μ 0)) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ (Fin.succ i)) := by
          rw [← ih (fun i => f (Fin.succ i)) (fun i => hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/- English proof (translation)
Set `e` to `(Fintype.equivFin ι).symm`. Rewrite using `[← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`. Repeatedly rewrite using `[← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]`. Conclude with `lintegral_pi_fin_prod_eq_prod_lintegral (fun i => f (e i)) (fun i => hf _)`.
-/
private theorem lintegral_pi_fintype_prod_eq_prod_lintegral {ι : Type*} [Fintype ι] {E : Type*} [MeasurableSpace E]
    {μ : ι → Measure E} [∀ i, SigmaFinite (μ i)] (f : ι → E → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_pi_fin_prod_eq_prod_lintegral (fun i => f (e i)) (fun i => hf _)

/- English proof (translation)
Conclude with `lintegral_pi_fintype_prod_eq_prod_lintegral (fun i y => ENNReal.ofReal (f i y)) (fun i => (hfm i).ennreal_ofReal)`.
-/
theorem lintegral_pi_prod_ofReal {ι : Type*} [Fintype ι] {E : Type*} [MeasurableSpace E] (μ : ι → Measure E)
    [∀ i, SigmaFinite (μ i)] (f : ι → E → ℝ) (hf0 : ∀ i x, 0 ≤ f i x) (hfm : ∀ i, Measurable (f i))
    (hfin : ∀ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂(μ i) ≠ ⊤) :
    ∫⁻ x, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂(μ i) := by
  exact lintegral_pi_fintype_prod_eq_prod_lintegral (fun i y => ENNReal.ofReal (f i y)) (fun i => (hfm i).ennreal_ofReal)

/- English proof (translation)
Establish `hJ : Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => JacV (Matrix.diagonal cv))`. Unfold `JacV`. Use `continuous_finset_prod _ fun l hl => ?_` and prove the remaining obligations. Establish `h : l ≤ D.R.rS + 1` using `(Finset.mem_Icc.mp hl).2.trans (Nat.le_succ _)`. Simplify using `only [modC, Dl, dif_pos h]`.

Use `fun_prop`. Unfold `wtV`. Conclude with `((gv_diag_cont u u').pow _).mul hJ`.
-/
theorem wtV_cont (u u' : D.what₂.Word) : Continuous (wtV u u') := by
  have hJ : Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => JacV (Matrix.diagonal cv)) := by
    unfold JacV
    refine continuous_finset_prod _ fun l hl => ?_
    have h : l ≤ D.R.rS + 1 := (Finset.mem_Icc.mp hl).2.trans (Nat.le_succ _)
    simp only [modC, Dl, dif_pos h]
    fun_prop
  unfold wtV
  exact ((gv_diag_cont u u').pow _).mul hJ

/- English proof (translation)
Take `⟨Cv, a, a', L, hpos, hCoo, haa, hL, hint⟩` from `h`. Use `haveI h2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by`. Rewrite using `[← withDensity_const]`. Conclude with `SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall fun _ => by norm_num)`. Use `haveI : SigmaFinite (dcV (D := D)) := by`.

Unfold `dcV`. Use `infer_instance`. Establish `hGm : MeasurableSet (Good X u u')`. Rewrite using `[good_eq_pi X u u']`. Conclude with `MeasurableSet.univ_pi fun _ => goodV_meas u u'`.

Establish `hwm : Measurable fun c : Cinf X => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c)`. Use `ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)` and prove the remaining obligations. Use `show Measurable fun c : Cinf X => ∏ v, wtV u u' (c v)`. Conclude with `Finset.measurable_prod _ fun v _ => (wtV_cont u u').measurable.comp (measurable_pi_apply v)`. Establish `hFm : ∀ v, Measurable fun x => ENNReal.ofReal (Cv v * wtV u u' x * L v x)` using `fun v => ((measurable_const.mul (wtV_cont u u').measurable).mul (hpos v).2.2.2.1).ennreal_ofReal`.

Unfold `intOOe nuM`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul_non_measurable _ hwm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem hGm] with c hc`.

Establish `hcv : ∀ v, c v ∈ GoodV u u'`. Rewrite `hc` using `[good_eq_pi X u u']`. Conclude with `fun v => hc v (Set.mem_univ v)`. Establish `hOO : hilbertSchmidtSqGram X u u' sc c = ∏ v, L v (c v)`. Unfold `hilbertSchmidtSqGram`.

Rewrite using `[hilbert_schmidt_tensor_product_factor]`. Conclude with `Finset.prod_congr rfl fun v _ => hL c hc v`. Establish `hnn : 0 ≤ (∏ v, Cv v) * ∏ v, wtV u u' (c v)` using `mul_nonneg (Finset.prod_nonneg fun v _ => (hpos v).1) (Finset.prod_nonneg fun v _ => wtV_nonneg u u' (hcv v))`. Simplify using `only [Pi.mul_apply]`. Rewrite using `[hOO, hCoo, show wt X u u' c = ∏ v, wtV u u' (c v) from rfl, ← ENNReal.ofReal_mul hnn, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Conclude with `ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (mul_nonneg (hpos v).1 (wtV_nonneg u u' (hcv v))) ((hpos v).2.2.2.2 _)`. Use `_ = ∏ v, ∫⁻ x in GoodV u u', ENNReal.ofReal (Cv v * wtV u u' x * L v x) ∂(dcV (D := D)) := by`. Rewrite using `[good_eq_pi X u u', show dcInf X = Measure.pi fun _ => dcV (D := D) from rfl, Measure.restrict_pi_pi]`. Conclude with `lintegral_pi_fintype_prod_eq_prod_lintegral (fun v x => ENNReal.ofReal (Cv v * wtV u u' x * L v x)) hFm`. Use `_ ≤ ∏ v, ENNReal.ofReal (a v * a' v / X.dv v) := Finset.prod_le_prod' fun v _ => hint v`.

Use `_ = ENNReal.ofReal (∏ v, (a v * a' v / X.dv v)) := (ENNReal.ofReal_prod_of_nonneg fun v _ => div_nonneg (mul_nonneg (hpos v).2.1 (hpos v).2.2.1) (hd v).le).symm`. Use `_ ≤ ENNReal.ofReal (1 / degX X) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Finset.prod_div_distrib, degX]`. Conclude with `div_le_div_of_nonneg_right haa (Finset.prod_pos fun v _ => hd v).le`.
-/
theorem intOOe_le_of_loc (u u' : D.what₂.Word) (sc : ℝ) (hd : ∀ v, 0 < X.dv v) (h : LocEnergy X u u' sc) :
    intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X) := by
  obtain ⟨Cv, a, a', L, hpos, hCoo, haa, hL, hint⟩ := h
  haveI h2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    rw [← withDensity_const]
    exact SigmaFinite.withDensity_of_ne_top (Filter.Eventually.of_forall fun _ => by norm_num)
  haveI : SigmaFinite (dcV (D := D)) := by
    unfold dcV
    infer_instance
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq_pi X u u']
    exact MeasurableSet.univ_pi fun _ => goodV_meas u u'
  have hwm : Measurable fun c : Cinf X => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    show Measurable fun c : Cinf X => ∏ v, wtV u u' (c v)
    exact Finset.measurable_prod _ fun v _ => (wtV_cont u u').measurable.comp (measurable_pi_apply v)
  have hFm : ∀ v, Measurable fun x => ENNReal.ofReal (Cv v * wtV u u' x * L v x) := fun v =>
    ((measurable_const.mul (wtV_cont u u').measurable).mul (hpos v).2.2.2.1).ennreal_ofReal
  unfold intOOe nuM
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hwm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc _ = ∫⁻ c, ∏ v, ENNReal.ofReal (Cv v * wtV u u' (c v) * L v (c v)) ∂((dcInf X).restrict (Good X u u')) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem hGm] with c hc
        have hcv : ∀ v, c v ∈ GoodV u u' := by
          rw [good_eq_pi X u u'] at hc
          exact fun v => hc v (Set.mem_univ v)
        have hOO : hilbertSchmidtSqGram X u u' sc c = ∏ v, L v (c v) := by
          unfold hilbertSchmidtSqGram
          rw [hilbert_schmidt_tensor_product_factor]
          exact Finset.prod_congr rfl fun v _ => hL c hc v
        have hnn : 0 ≤ (∏ v, Cv v) * ∏ v, wtV u u' (c v) :=
          mul_nonneg (Finset.prod_nonneg fun v _ => (hpos v).1)
            (Finset.prod_nonneg fun v _ => wtV_nonneg u u' (hcv v))
        simp only [Pi.mul_apply]
        rw [hOO, hCoo, show wt X u u' c = ∏ v, wtV u u' (c v) from rfl,
          ← ENNReal.ofReal_mul hnn, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact ENNReal.ofReal_prod_of_nonneg fun v _ =>
          mul_nonneg (mul_nonneg (hpos v).1 (wtV_nonneg u u' (hcv v))) ((hpos v).2.2.2.2 _)
    _ = ∏ v, ∫⁻ x in GoodV u u', ENNReal.ofReal (Cv v * wtV u u' x * L v x) ∂(dcV (D := D)) := by
        rw [good_eq_pi X u u', show dcInf X = Measure.pi fun _ => dcV (D := D) from rfl,
          Measure.restrict_pi_pi]
        exact lintegral_pi_fintype_prod_eq_prod_lintegral (fun v x => ENNReal.ofReal (Cv v * wtV u u' x * L v x)) hFm
    _ ≤ ∏ v, ENNReal.ofReal (a v * a' v / X.dv v) := Finset.prod_le_prod' fun v _ => hint v
    _ = ENNReal.ofReal (∏ v, (a v * a' v / X.dv v)) :=
        (ENNReal.ofReal_prod_of_nonneg fun v _ =>
          div_nonneg (mul_nonneg (hpos v).2.1 (hpos v).2.2.1) (hd v).le).symm
    _ ≤ ENNReal.ofReal (1 / degX X) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.prod_div_distrib, degX]
        exact div_le_div_of_nonneg_right haa (Finset.prod_pos fun v _ => hd v).le

def StepLocEnergy : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → (∀ v, 0 < X.dv v) ∧ LocEnergy X u u' sc

/- English proof (translation)
Introduce `D X u u' sc hsc hP hC`. Take `⟨hd, hL⟩` from `h D X u u' sc hsc hP hC`. Conclude with `intOOe_le_of_loc X u u' sc hd hL`.
-/
theorem stepEnergy_of_loc (h : StepLocEnergy) : Formalism.L2.SG.RealObj.InfCut.StepEnergy := by
  intro D X u u' sc hsc hP hC
  obtain ⟨hd, hL⟩ := h D X u u' sc hsc hP hC
  exact intOOe_le_of_loc X u u' sc hd hL

end Formalism.L2.SG.RealObj.EnergyCut
