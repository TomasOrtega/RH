import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamePartRight

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

/- English proof (translation)
Use function extensionality and compare the values at `y0`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖f y0‖` using `norm_pos_iff.2 hne`. Establish `hN : {y | ‖f y - f y0‖ < ‖f y0‖ / 2} ∈ 𝓝 y0` using `(isOpen_lt (hf.sub continuous_const).norm continuous_const).mem_nhds (by simpa using hpos)`. Take `⟨C, hCa, hCu, hC⟩` from `local_compact_nhds hN`.

Take `⟨U, hU, hyU, hUC⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := Y)).mem_nhds_iff.mp hCa`. Establish `hUc : IsCompact U` using `hC.of_isClosed_subset hU.1 hUC`. Establish `hk : U.indicator (1 : Y → ℂ) ∈ GlobalTheory.WeilM.SB Y` using `⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hU).isLocallyConstant, HasCompactSupport.intro' hUc hU.isClosed (fun x hx => Set.indicator_of_notMem hx _)⟩`. Establish `h0 : ∫ y in U, f y ∂ν = 0`. Rewrite using `[← h _ hk, ← integral_indicator hU.2.measurableSet]`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hy : y ∈ U <;> simp [hy]`. Establish `hfin : ν U < ∞` using `hUc.measure_lt_top`. Establish `hνpos : 0 < ν.real U`. Use `ENNReal.toReal_pos (hU.2.measure_pos ν ⟨y0, hyU⟩).ne' hfin.ne` and prove the remaining obligations.

Establish `hint : IntegrableOn f U ν` using `hf.continuousOn.integrableOn_compact hUc`. Establish `hc : ∫ y in U, (f y - f y0) ∂ν = - (ν.real U • f y0)`. Rewrite using `[integral_sub hint (integrableOn_const hfin.ne), h0, setIntegral_const, zero_sub]`. Establish `hb : ‖∫ y in U, (f y - f y0) ∂ν‖ ≤ ‖f y0‖ / 2 * ν.real U` using `norm_setIntegral_le_of_norm_le_const hfin fun y hy => (hCu (hUC hy)).le`. Rewrite `hb` using `[hc, norm_neg, norm_smul, Real.norm_of_nonneg hνpos.le]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eq_zero_of_orth_SB {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (f : Y → ℂ) (hf : Continuous f)
    (h : ∀ k ∈ GlobalTheory.WeilM.SB Y, ∫ y, f y * conj (k y) ∂ν = 0) : f = 0 := by
  funext y0
  by_contra hne
  have hpos : 0 < ‖f y0‖ := norm_pos_iff.2 hne
  have hN : {y | ‖f y - f y0‖ < ‖f y0‖ / 2} ∈ 𝓝 y0 :=
    (isOpen_lt (hf.sub continuous_const).norm continuous_const).mem_nhds (by simpa using hpos)
  obtain ⟨C, hCa, hCu, hC⟩ := local_compact_nhds hN
  obtain ⟨U, hU, hyU, hUC⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := Y)).mem_nhds_iff.mp hCa
  have hUc : IsCompact U := hC.of_isClosed_subset hU.1 hUC
  have hk : U.indicator (1 : Y → ℂ) ∈ GlobalTheory.WeilM.SB Y :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hU).isLocallyConstant,
      HasCompactSupport.intro' hUc hU.isClosed (fun x hx => Set.indicator_of_notMem hx _)⟩
  have h0 : ∫ y in U, f y ∂ν = 0 := by
    rw [← h _ hk, ← integral_indicator hU.2.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ U <;> simp [hy]
  have hfin : ν U < ∞ := hUc.measure_lt_top
  have hνpos : 0 < ν.real U := by
    refine ENNReal.toReal_pos (hU.2.measure_pos ν ⟨y0, hyU⟩).ne' hfin.ne
  have hint : IntegrableOn f U ν := hf.continuousOn.integrableOn_compact hUc
  have hc : ∫ y in U, (f y - f y0) ∂ν = - (ν.real U • f y0) := by
    rw [integral_sub hint (integrableOn_const hfin.ne), h0, setIntegral_const, zero_sub]
  have hb : ‖∫ y in U, (f y - f y0) ∂ν‖ ≤ ‖f y0‖ / 2 * ν.real U :=
    norm_setIntegral_le_of_norm_le_const hfin fun y hy => (hCu (hUC hy)).le
  rw [hc, norm_neg, norm_smul, Real.norm_of_nonneg hνpos.le] at hb
  nlinarith

/- English proof (translation)
Take `⟨B, hB⟩` from `hB`. Use `haveI : (lam.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure lam ν`. Use `haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m`. Establish `hmap` using `Measure.isAddLeftInvariant_eq_smul (m.map e) (lam.prod ν)`. Establish `hcpos` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map e) (lam.prod ν)`.

Establish `hemb : MeasurableEmbedding e` using `e.toHomeomorph.measurableEmbedding`. Use `set v : Z × Y → ℂ := fun p => u (e.symm p) with hv`. Establish `hvc : Continuous v` using `hu.comp e.symm.continuous`. Establish `hvB : ∀ p, ‖v p‖ ≤ B` using `fun p => hB _`. Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hvB (Classical.choice (by infer_instance : Nonempty (Z × Y))))`.

Establish `hkey : ∀ k ∈ GlobalTheory.WeilM.SB Y, ∀ z, ∫ y, v (z, y) * conj (k y) ∂ν = 0`. Introduce `k hk`. Establish `hkc : Continuous k` using `hk.1.continuous`. Establish `hki : Integrable k ν` using `hkc.integrable_of_hasCompactSupport hk.2`. Establish `hcc : Continuous fun y => conj (k y)` using `Complex.continuous_conj.comp hkc`.

Establish `hw : (fun z => ∫ y, v (z, y) * conj (k y) ∂ν) = 0`. Use `hE _ ?_ ⟨∫ y, B * ‖k y‖ ∂ν, fun z => ?_⟩ fun t ht => ?_` and prove the remaining obligations. Use `continuous_of_dominated (bound := fun y => B * ‖k y‖) (fun z => ?_) (fun z => ?_) (hki.norm.const_mul B) ?_` and prove the remaining obligations. Conclude with `((hvc.comp (Continuous.prodMk_right z)).mul hcc).aestronglyMeasurable`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, RCLike.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)`. Use `Eventually.of_forall fun y => ?_` and prove the remaining obligations. Conclude with `(hvc.comp (Continuous.prodMk_left y)).mul continuous_const`. Use `(norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hki.norm.const_mul B) (Eventually.of_forall fun y => ?_)) show ‖v (z, y) * conj (k y)‖ ≤ B * ‖k y‖` and prove the remaining obligations.

Rewrite using `[norm_mul, RCLike.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)`. Take `⟨htc, hti⟩` from `hT t ht set F : Z × Y → ℂ := fun p => v p * conj (t p.1 * k p.2) with hF`. Establish `hFc : Continuous F` using `hvc.mul (Complex.continuous_conj.comp ((htc.comp continuous_fst).mul (hkc.comp continuous_snd)))`. Establish `hFi : Integrable F (lam.prod ν)`.

Use `((hti.mul_prod hki).norm.const_mul B).mono' hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [hF, norm_mul, RCLike.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_right (hvB _) (by positivity)`. Establish `h1 : ∫ x, u x * conj (t (e x).1 * k (e x).2) ∂m = ((Measure.addHaarScalarFactor (m.map e) (lam.prod ν) : ℝ≥0) : ℝ) • ∫ p, F p ∂(lam.prod ν)`. Establish `: ∫ p, F p ∂(m.map e) = ∫ x, F (e x) ∂m` using `hemb.integral_map F`.

Establish `h2 : ∀ x, F (e x) = u x * conj (t (e x).1 * k (e x).2)` using `fun x => by simp [hF, hv]`. Simplify using `only [h2] at this`. Rewrite using `[← this]`. Use `conv_lhs => rw [hmap]`. Rewrite using `[integral_smul_nnreal_measure, NNReal.smul_def]`.

Establish `h3 : ∫ p, F p ∂(lam.prod ν) = 0`. Use `h1.symm.trans (h t ht k hk)` as an intermediate fact. Conclude with `(smul_eq_zero.1 this).resolve_left (by exact_mod_cast hcpos.ne')`. Rewrite `h3` using `[integral_prod F hFi]`. Rewrite using `[← h3]`.

Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [hF, map_mul]`. Rewrite using `[← integral_mul_const]`. Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`.

Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Conclude with `congrFun hw z`. Use function extensionality and compare the values at `x`. Establish `h0` using `eq_zero_of_orth_SB ν (fun y => v ((e x).1, y)) (hvc.comp (Continuous.prodMk_right _)) (fun k hk => hkey k hk (e x).1)`.

Use `congrFun h0 (e x).2` as an intermediate fact. Simplify `this` using `[hv]`.
-/
theorem total_of_split {G Z Y : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [LocallyCompactSpace Z] [SecondCountableTopology Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : G ≃ₜ+ Z × Y) (m : Measure G) [m.IsAddHaarMeasure] (lam : Measure Z) [lam.IsAddHaarMeasure]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (T : Set (Z → ℂ)) (hT : ∀ t ∈ T, Continuous t ∧ Integrable t lam)
    (hE : ∀ w : Z → ℂ, Continuous w → (∃ B : ℝ, ∀ z, ‖w z‖ ≤ B) → (∀ t ∈ T, ∫ z, w z * conj (t z) ∂lam = 0) → w = 0)
    (u : G → ℂ) (hu : Continuous u) (hB : ∃ B : ℝ, ∀ x, ‖u x‖ ≤ B)
    (h : ∀ t ∈ T, ∀ k ∈ GlobalTheory.WeilM.SB Y, ∫ x, u x * conj (t (e x).1 * k (e x).2) ∂m = 0) : u = 0 := by
  obtain ⟨B, hB⟩ := hB
  haveI : (lam.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure lam ν
  haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  have hmap := Measure.isAddLeftInvariant_eq_smul (m.map e) (lam.prod ν)
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map e) (lam.prod ν)
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  set v : Z × Y → ℂ := fun p => u (e.symm p) with hv
  have hvc : Continuous v := hu.comp e.symm.continuous
  have hvB : ∀ p, ‖v p‖ ≤ B := fun p => hB _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hvB (Classical.choice (by infer_instance : Nonempty (Z × Y))))
  have hkey : ∀ k ∈ GlobalTheory.WeilM.SB Y, ∀ z, ∫ y, v (z, y) * conj (k y) ∂ν = 0 := by
    intro k hk
    have hkc : Continuous k := hk.1.continuous
    have hki : Integrable k ν := hkc.integrable_of_hasCompactSupport hk.2
    have hcc : Continuous fun y => conj (k y) := Complex.continuous_conj.comp hkc
    have hw : (fun z => ∫ y, v (z, y) * conj (k y) ∂ν) = 0 := by
      refine hE _ ?_ ⟨∫ y, B * ‖k y‖ ∂ν, fun z => ?_⟩ fun t ht => ?_
      · refine continuous_of_dominated (bound := fun y => B * ‖k y‖) (fun z => ?_) (fun z => ?_) (hki.norm.const_mul B) ?_
        · exact ((hvc.comp (Continuous.prodMk_right z)).mul hcc).aestronglyMeasurable
        · refine Eventually.of_forall fun y => ?_
          rw [norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)
        · refine Eventually.of_forall fun y => ?_
          exact (hvc.comp (Continuous.prodMk_left y)).mul continuous_const
      · refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hki.norm.const_mul B) (Eventually.of_forall fun y => ?_))
        show ‖v (z, y) * conj (k y)‖ ≤ B * ‖k y‖
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_right (hvB _) (norm_nonneg _)
      · obtain ⟨htc, hti⟩ := hT t ht
        set F : Z × Y → ℂ := fun p => v p * conj (t p.1 * k p.2) with hF
        have hFc : Continuous F := hvc.mul (Complex.continuous_conj.comp ((htc.comp continuous_fst).mul (hkc.comp continuous_snd)))
        have hFi : Integrable F (lam.prod ν) := by
          refine ((hti.mul_prod hki).norm.const_mul B).mono' hFc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
          simp only [hF, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_right (hvB _) (by positivity)
        have h1 : ∫ x, u x * conj (t (e x).1 * k (e x).2) ∂m = ((Measure.addHaarScalarFactor (m.map e) (lam.prod ν) : ℝ≥0) : ℝ) • ∫ p, F p ∂(lam.prod ν) := by
          have : ∫ p, F p ∂(m.map e) = ∫ x, F (e x) ∂m := hemb.integral_map F
          have h2 : ∀ x, F (e x) = u x * conj (t (e x).1 * k (e x).2) := fun x => by simp [hF, hv]
          simp only [h2] at this
          rw [← this]
          conv_lhs => rw [hmap]
          rw [integral_smul_nnreal_measure, NNReal.smul_def]
        have h3 : ∫ p, F p ∂(lam.prod ν) = 0 := by
          have := h1.symm.trans (h t ht k hk)
          exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hcpos.ne')
        rw [integral_prod F hFi] at h3
        rw [← h3]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hF, map_mul]
        rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
    intro z
    exact congrFun hw z
  funext x
  have h0 := eq_zero_of_orth_SB ν (fun y => v ((e x).1, y)) (hvc.comp (Continuous.prodMk_right _))
    (fun k hk => hkey k hk (e x).1)
  have := congrFun h0 (e x).2
  simpa [hv] using this

section Poly

variable {D : D7} {m n : ℕ}

def coordV (k : D.what₂.Tau × Fin m × Fin n × Bool) (z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2.2 then conj (z k.1 k.2.1 k.2.2.1) else z k.1 k.2.1 k.2.2.1

def polyV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℂ :=
  evalPoly q fun τ => Matrix.of (z τ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem polyV_eq (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) (z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    polyV q z = MvPolynomial.eval (fun k => coordV k z) q := rfl

def coordL (k : D.what₂.Tau × Fin m × Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) k.1))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordL_apply (k : D.what₂.Tau × Fin m × Fin n) (z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    coordL k z = z k.1 k.2.1 k.2.2 := rfl

/- English proof (translation)
Take `⟨τ, i, j, b⟩` from `k`. Consider the cases of `b`. Conclude with `(coordL (D := D) (τ, i, j)).hasTemperateGrowth`. Conclude with `(((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp (coordL (D := D) (τ, i, j))).hasTemperateGrowth`.
-/
theorem coordV_temperate (k : D.what₂.Tau × Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coordV (D := D) k) := by
  obtain ⟨τ, i, j, b⟩ := k
  cases b
  · exact (coordL (D := D) (τ, i, j)).hasTemperateGrowth
  · exact (((Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp (coordL (D := D) (τ, i, j))).hasTemperateGrowth

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: polyV (D` using `D) (m := m) (n := n) (MvPolynomial.C a) = fun _ => a := by`. Use function extensionality and compare the values at `z`. Simplify using `[polyV_eq]`.

Rewrite using `[this]`. Conclude with `Function.HasTemperateGrowth.const a`. Consider the case `add p q hp hq`. Establish `: polyV (p + q) = fun z => polyV p z + polyV q z`. Use function extensionality and compare the values at `z`.

Simplify using `[polyV_eq]`. Rewrite using `[this]`. Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Establish `: polyV (p * MvPolynomial.X k) = fun z => polyV p z * coordV k z`.

Use function extensionality and compare the values at `z`. Simplify using `[polyV_eq]`. Rewrite using `[this]`. Conclude with `hp.mul (coordV_temperate k)`.
-/
theorem polyV_temperate (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (polyV q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : polyV (D := D) (m := m) (n := n) (MvPolynomial.C a) = fun _ => a := by
      funext z; simp [polyV_eq]
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : polyV (p + q) = fun z => polyV p z + polyV q z := by
      funext z; simp [polyV_eq]
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : polyV (p * MvPolynomial.X k) = fun z => polyV p z * coordV k z := by
      funext z; simp [polyV_eq]
    rw [this]; exact hp.mul (coordV_temperate k)

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨MvPolynomial.C (conj a), fun z => by simp [polyV_eq]⟩`. Consider the case `add p q hp hq`. Take `⟨p', hp⟩` from `hp`. Take `⟨q', hq⟩` from `hq`.

Use `⟨p' + q', fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hp z`. Establish `h2` using `hq z`. Simplify using `only [polyV_eq, map_add] at h1 h2 ⊢`. Rewrite using `[h1, h2]`.

Consider the case `mul_X p k hp`. Take `⟨p', hp⟩` from `hp`. Use `⟨p' * MvPolynomial.X (k.1, k.2.1, k.2.2.1, !k.2.2.2), fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hp z`. Simplify using `only [polyV_eq, map_mul, MvPolynomial.eval_X] at h1 ⊢`.

Rewrite using `[h1]`. Use `congr 1`. Take `⟨τ, i, j, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [coordV]`.
-/
theorem exists_conj_polyV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∃ q' : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ, ∀ z, conj (polyV q z) = polyV q' z := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C (conj a), fun z => by simp [polyV_eq]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [polyV_eq, map_add] at h1 h2 ⊢
    rw [h1, h2]
  | mul_X p k hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * MvPolynomial.X (k.1, k.2.1, k.2.2.1, !k.2.2.2), fun z => ?_⟩
    have h1 := hp z
    simp only [polyV_eq, map_mul, MvPolynomial.eval_X] at h1 ⊢
    rw [h1]
    congr 1
    obtain ⟨τ, i, j, b⟩ := k
    cases b <;> simp [coordV]

def polyAlg (D : D7) (m n : ℕ) : Subalgebra ℂ ((D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) (coordV (D := D) (m := m) (n := n))).range

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => funext z`. Simplify using `[polyV_eq]`. Consider the case `add p q hp hq => funext z`. Simplify using `[polyV_eq, hp, hq]`.

Consider the case `mul_X p k hp => funext z`. Simplify using `[polyV_eq, hp]`.
-/
theorem aeval_coordV (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ) (coordV (D := D) (m := m) (n := n)) q = polyV q := by
  induction q using MvPolynomial.induction_on with
  | C a => funext z; simp [polyV_eq]
  | add p q hp hq => funext z; simp [polyV_eq, hp, hq]
  | mul_X p k hp => funext z; simp [polyV_eq, hp]

end Poly

section Gauss

variable {D : D7} {p : ℕ}

/- English proof (translation)
Establish `h : (V1 D).gram = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `(Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j).trans ?_` and prove the remaining obligations. Use `show (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0`. Both sides reduce to the same expression.

Use `show (HSpace.gram (V1 D)).map (tauE D τ) = 1`. Rewrite using `[h]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem gram_at_place_rank_one (τ : D.what₂.Tau) : gramAt D (V1 D) τ = 1 := by
  have h : (V1 D).gram = 1 := by
    refine Matrix.ext fun i j => ?_
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j).trans ?_
    show (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    rfl
  show (HSpace.gram (V1 D)).map (tauE D τ) = 1
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

open scoped ComplexOrder in
/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_one _, by simp, by simpa using Matrix.PosDef.one⟩`.
-/
theorem cartan_one (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 :=
  ⟨mul_one _, by simp, by simpa using Matrix.PosDef.one⟩

def sqSum (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) : ℝ :=
  ∑ τ, |l τ| * ∑ j, ∑ i, ‖z τ i j‖ ^ 2

def gaussR (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) : ℝ :=
  Real.exp (-(2 * Real.pi) * sqSum l z)

/- English proof (translation)
Rewrite using `[gauss, gaussR, Complex.ofReal_exp, sqSum]`. Use `congr 1`. Use `push_cast`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[gram_at_place_rank_one, mul_one, Matrix.mul_one, Matrix.trace]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Complex.conj_mul' (z τ i j)]`. Both sides reduce to the same expression.
-/
theorem gauss_eq (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) :
    gauss (V1 D) l (fun _ => 1) (fun τ => Matrix.of (z τ)) = (gaussR l z : ℂ) := by
  rw [gauss, gaussR, Complex.ofReal_exp, sqSum]
  congr 1
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [gram_at_place_rank_one, mul_one, Matrix.mul_one, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.conj_mul' (z τ i j)]
  rfl

/- English proof (translation)
Unfold `gaussR sqSum`. Use `fun_prop`.
-/
theorem continuous_gaussR (l : D.what₂.Tau → ℝ) : Continuous (gaussR (D := D) (p := p) l) := by
  unfold gaussR sqSum
  fun_prop

/- English proof (translation)
Rewrite using `[one_mul, gaussR]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Establish `hS : ∀ τ, 0 ≤ ∑ j, ∑ i, ‖z τ i j‖ ^ 2` using `fun τ => by positivity`. Establish `h1 : L * ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2 ≤ sqSum l z`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right (hL τ) (hS τ)`. Establish `h2 : ‖z‖ ^ 2 ≤ ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2`. Establish `h3 : ‖z‖ ≤ Real.sqrt (∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun τ => (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => Real.le_sqrt_of_sq_le ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hp` using `Real.pi_pos`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 hL0.le]`.
-/
theorem gaussR_le (l : D.what₂.Tau → ℝ) (L : ℝ) (hL0 : 0 < L) (hL : ∀ τ, L ≤ |l τ|)
    (z : D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) :
    gaussR l z ≤ 1 * Real.exp (-(2 * Real.pi * L) * ‖z‖ ^ 2) := by
  rw [one_mul, gaussR]
  refine Real.exp_le_exp.2 ?_
  have hS : ∀ τ, 0 ≤ ∑ j, ∑ i, ‖z τ i j‖ ^ 2 := fun τ => by positivity
  have h1 : L * ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2 ≤ sqSum l z := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right (hL τ) (hS τ)
  have h2 : ‖z‖ ^ 2 ≤ ∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2 := by
    have h3 : ‖z‖ ≤ Real.sqrt (∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun τ => (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => Real.le_sqrt_of_sq_le ?_
      calc ‖z τ i j‖ ^ 2 ≤ ∑ i, ‖z τ i j‖ ^ 2 :=
            Finset.single_le_sum (f := fun i => ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
        _ ≤ ∑ j, ∑ i, ‖z τ i j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ∑ i, ‖z τ i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
        _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ j, ∑ i, ‖z τ i j‖ ^ 2) (fun τ _ => hS τ) (Finset.mem_univ τ)
    calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ τ, ∑ j, ∑ i, ‖z τ i j‖ ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun τ _ => hS τ)
  have hp := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left h2 hL0.le]

end Gauss

/- English proof (translation)
Introduce `hEuc D p θ hθ l hl μ 𝓕 hμ u hu hB horth`. Use `haveI := hμ.1`. Use `haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩`. Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F`. Use `haveI : TotallyDisconnectedSpace (Af D.host.F) := GlobalTheory.TamePartR.totallyDisconnected_finiteAdele D.host.F`. Take `⟨e0⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)`.

Use `haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace`. Use `haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology`. Use `haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space`. Use `haveI : TotallyDisconnectedSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.symm.totallyDisconnectedSpace`. Use `letI : MeasurableSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _`.

Use `haveI : BorelSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx D (V1 D).rank p) := ⟨rfl⟩`. Use `haveI := (lattice_Mx D (V1 D).rank p).1`. Take `⟨e, he⟩` from `GlobalTheory.RegSch.IkSchwartz.exists_split hθ (V1 D).rank p`. Set `lam : Measure (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ)` to `Measure.addHaar`.

Set `ν : Measure (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D)` to `Measure.addHaar`. Take `⟨f, hf⟩` from `GlobalTheory.GaussSchwartz.exists_schwartz_gauss D p (V1 D) l hl (fun _ => 1) (fun τ => by`. Rewrite using `[gram_at_place_rank_one]`. Conclude with `cartan_one _)`. Choose the witnesses or unpack the hypotheses as in `⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 < L ∧ ∀ τ, L ≤ |l τ| := by`.

Break down `isEmpty_or_nonempty D.what₂.Tau with h | h` into its components or cases. Conclude with `⟨1, one_pos, fun τ => (h.false τ).elim⟩`. Take `⟨τ₀, -, h₀⟩` from `Finset.exists_min_image Finset.univ (fun τ => |l τ|) Finset.univ_nonempty`. Conclude with `⟨|l τ₀|, abs_pos.2 (hl τ₀), fun τ => h₀ τ (Finset.mem_univ τ)⟩`. Use `total_of_split e μ lam ν {t | ∃ q : MvPolynomial (D.what₂.Tau × Fin (V1 D).rank × Fin p × Bool) ℂ, ∀ z, t z = polyV q z * (gaussR l z : ℂ)} ?_ ?_ u hu hB ?_` and prove the remaining obligations.

Introduce and unpack `t ⟨q, hq⟩`. Establish `ht : t = SchwartzMap.smulLeftCLM ℂ (polyV q) f`. Use function extensionality and compare the values at `z`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (polyV_temperate q), hq, hf, gauss_eq]`. Both sides reduce to the same expression.

Rewrite using `[ht]`. Conclude with `⟨SchwartzMap.continuous _, SchwartzMap.integrable _⟩`. Introduce `w hw hwB hwt`. Use `hEuc _ lam (D.what₂.Tau × Fin (V1 D).rank × Fin p) coordL (fun z hz => ?_) (polyAlg D _ p) (fun k => ?_) (fun k => ?_) (gaussR l) (continuous_gaussR l) (fun z => Real.exp_pos _) 1 (2 * Real.pi * L) (by positivity) (fun z => ?_) w hw hwB ?_` and prove the remaining obligations. Use function extensionality and compare the values at `τ i j`.

Conclude with `hz (τ, i, j)`. Use `⟨MvPolynomial.X (k.1, k.2.1, k.2.2, false), ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.aeval_X _ _).trans ?_` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[coordV, coordL_apply]`.

Use `⟨MvPolynomial.X (k.1, k.2.1, k.2.2, true), ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.aeval_X _ _).trans ?_` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Simplify using `[coordV, coordL_apply]`. Use `gaussR_le l L hL0 hL z` as an intermediate fact.

Simplify `this` using `[neg_mul]`. Introduce and unpack `P ⟨q, rfl⟩`. Take `⟨q', hq'⟩` from `exists_conj_polyV q`. Use `hwt (fun z => polyV q' z * (gaussR l z : ℂ)) ⟨q', fun z => rfl⟩` as an intermediate fact. Rewrite using `[← this]`.

Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Establish `h1 : (MvPolynomial.aeval (R` using `ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q = polyV q := aeval_coordV q`. Use `show w z * ((MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q) z * _ = _`. Rewrite using `[h1]`. Use `show w z * polyV q z * (gaussR l z : ℂ) = w z * conj (polyV q' z * (gaussR l z : ℂ))`.

Rewrite using `[map_mul, ← hq' z, Complex.conj_conj, Complex.conj_ofReal, mul_assoc]`. Introduce and unpack `t ⟨q, hq⟩ k hk`. Use `horth (fun x => evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) * k (fun i j => finPart D (x i j))) (Submodule.subset_span ⟨q, k, hk, rfl⟩)` as an intermediate fact. Rewrite using `[← this]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Use `show u x * conj (t (e x).1 * k (e x).2) = u x * conj (evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) * k (fun i j => finPart D (x i j)))`. Rewrite using `[hq, he, ← gauss_eq]`. Both sides reduce to the same expression.
-/
theorem fockTotal_of_eucTotal : EucTotal → FockTotal := by
  intro hEuc D p θ hθ l hl μ 𝓕 hμ u hu hB horth
  haveI := hμ.1
  haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  haveI : TotallyDisconnectedSpace (Af D.host.F) := GlobalTheory.TamePartR.totallyDisconnected_finiteAdele D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
  haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
  haveI : TotallyDisconnectedSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.symm.totallyDisconnectedSpace
  letI : MeasurableSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
  haveI : BorelSpace (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (V1 D).rank p) := ⟨rfl⟩
  haveI := (lattice_Mx D (V1 D).rank p).1
  obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ (V1 D).rank p
  let lam : Measure (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) := Measure.addHaar
  let ν : Measure (Fin (V1 D).rank → Fin p → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
  obtain ⟨f, hf⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_gauss D p (V1 D) l hl (fun _ => 1) (fun τ => by
    rw [gram_at_place_rank_one]
    exact cartan_one _)
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 < L ∧ ∀ τ, L ≤ |l τ| := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (h.false τ).elim⟩
    · obtain ⟨τ₀, -, h₀⟩ := Finset.exists_min_image Finset.univ (fun τ => |l τ|) Finset.univ_nonempty
      exact ⟨|l τ₀|, abs_pos.2 (hl τ₀), fun τ => h₀ τ (Finset.mem_univ τ)⟩
  refine total_of_split e μ lam ν
    {t | ∃ q : MvPolynomial (D.what₂.Tau × Fin (V1 D).rank × Fin p × Bool) ℂ, ∀ z, t z = polyV q z * (gaussR l z : ℂ)}
    ?_ ?_ u hu hB ?_
  · rintro t ⟨q, hq⟩
    have ht : t = SchwartzMap.smulLeftCLM ℂ (polyV q) f := by
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (polyV_temperate q), hq, hf, gauss_eq]
      rfl
    rw [ht]
    exact ⟨SchwartzMap.continuous _, SchwartzMap.integrable _⟩
  · intro w hw hwB hwt
    refine hEuc _ lam (D.what₂.Tau × Fin (V1 D).rank × Fin p) coordL (fun z hz => ?_) (polyAlg D _ p) (fun k => ?_) (fun k => ?_)
      (gaussR l) (continuous_gaussR l) (fun z => Real.exp_pos _) 1 (2 * Real.pi * L) (by positivity) (fun z => ?_) w hw hwB ?_
    · funext τ i j
      exact hz (τ, i, j)
    · refine ⟨MvPolynomial.X (k.1, k.2.1, k.2.2, false), ?_⟩
      refine (MvPolynomial.aeval_X _ _).trans ?_
      funext z
      simp [coordV, coordL_apply]
    · refine ⟨MvPolynomial.X (k.1, k.2.1, k.2.2, true), ?_⟩
      refine (MvPolynomial.aeval_X _ _).trans ?_
      funext z
      simp [coordV, coordL_apply]
    · have := gaussR_le l L hL0 hL z
      simpa [neg_mul] using this
    · rintro P ⟨q, rfl⟩
      obtain ⟨q', hq'⟩ := exists_conj_polyV q
      have := hwt (fun z => polyV q' z * (gaussR l z : ℂ)) ⟨q', fun z => rfl⟩
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have h1 : (MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q = polyV q := aeval_coordV q
      show w z * ((MvPolynomial.aeval (R := ℂ) (S₁ := (D.what₂.Tau → Fin (V1 D).rank → Fin p → ℂ) → ℂ) (coordV (D := D) (m := (V1 D).rank) (n := p))) q) z * _ = _
      rw [h1]
      show w z * polyV q z * (gaussR l z : ℂ) = w z * conj (polyV q' z * (gaussR l z : ℂ))
      rw [map_mul, ← hq' z, Complex.conj_conj, Complex.conj_ofReal, mul_assoc]
  · rintro t ⟨q, hq⟩ k hk
    have := horth (fun x => evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) *
      k (fun i j => finPart D (x i j))) (Submodule.subset_span ⟨q, k, hk, rfl⟩)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show u x * conj (t (e x).1 * k (e x).2) = u x * conj (evalPoly q (fun τ => compAt θ τ x) * gauss (V1 D) l (fun _ => 1) (fun τ => compAt θ τ x) *
      k (fun i j => finPart D (x i j)))
    rw [hq, he, ← gauss_eq]
    rfl

end GlobalTheory.CompanionTheory.ThTot
end
