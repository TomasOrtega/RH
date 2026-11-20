import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CWIntegral

open PI.UpqRep GlobalTheory.CWDeriv

/- English proof (translation)
Establish `hker : LinearMap.ker T ≤ LinearMap.ker φ`. Introduce `s hs`. Rewrite `hs`, the goal using `[LinearMap.mem_ker]`. Establish `h1` using `h s`. Rewrite `h1` using `[hs, norm_zero, mul_zero]`.

Conclude with `norm_le_zero_iff.mp h1`. Set `ψ : LinearMap.range T →ₗ[ℂ] ℂ` to `((LinearMap.ker T).liftQ φ hker).comp T.quotKerEquivRange.symm.toLinearMap`. Establish `hψT : ∀ s, ψ ⟨T s, LinearMap.mem_range_self T s⟩ = φ s`. Introduce `s`. Establish `hq : T.quotKerEquivRange.symm ⟨T s, LinearMap.mem_range_self T s⟩ = (LinearMap.ker T).mkQ s` using `LinearMap.quotKerEquivRange_symm_apply_image T s _`.

Simplify using `only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.liftQ_apply]`. Establish `hbd : ∀ y : LinearMap.range T, ‖ψ y‖ ≤ max C 0 * ‖y‖`. Introduce and unpack `⟨y, s, rfl⟩`. Rewrite using `[hψT]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨Λ, hΛ, -⟩` from `exists_extension_norm_eq (LinearMap.range T) (ψ.mkContinuous (max C 0) hbd)`. Use `⟨Λ, fun s => ?_⟩` and prove the remaining obligations. Use `hΛ ⟨T s, LinearMap.mem_range_self T s⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.mkContinuous_apply, hψT]`. Conclude with `this`.
-/
theorem exists_functional {S E : Type} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : S →ₗ[ℂ] E) (φ : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ s, ‖φ s‖ ≤ C * ‖T s‖) :
    ∃ Λ : E →L[ℂ] ℂ, ∀ s, Λ (T s) = φ s := by
  have hker : LinearMap.ker T ≤ LinearMap.ker φ := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h1 := h s
    rw [hs, norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  let ψ : LinearMap.range T →ₗ[ℂ] ℂ :=
    ((LinearMap.ker T).liftQ φ hker).comp T.quotKerEquivRange.symm.toLinearMap
  have hψT : ∀ s, ψ ⟨T s, LinearMap.mem_range_self T s⟩ = φ s := by
    intro s
    have hq : T.quotKerEquivRange.symm ⟨T s, LinearMap.mem_range_self T s⟩ = (LinearMap.ker T).mkQ s :=
      LinearMap.quotKerEquivRange_symm_apply_image T s _
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hbd : ∀ y : LinearMap.range T, ‖ψ y‖ ≤ max C 0 * ‖y‖ := by
    rintro ⟨y, s, rfl⟩
    rw [hψT]
    calc ‖φ s‖ ≤ C * ‖T s‖ := h s
      _ ≤ max C 0 * ‖T s‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) (ψ.mkContinuous (max C 0) hbd)
  refine ⟨Λ, fun s => ?_⟩
  have := hΛ ⟨T s, LinearMap.mem_range_self T s⟩
  rw [LinearMap.mkContinuous_apply, hψT] at this
  exact this

variable {k r : ℕ}

def linOn (R : Rep k r) {V : Type} [AddCommGroup V] [Module ℂ V] (B : R.H → V)
    (ha : ∀ v ∈ R.sm, ∀ w ∈ R.sm, B (v + w) = B v + B w) (hs : ∀ (a : ℂ), ∀ v ∈ R.sm, B (a • v) = a • B v) :
    R.smSub →ₗ[ℂ] V where
  toFun v := B v
  map_add' v w := ha _ v.2 _ w.2
  map_smul' a v := hs a _ v.2

/- English proof (translation)
Use `revert hW`. Proceed by induction on `W with`. Consider the case `nil => intro _`. Both sides reduce to the same expression. Consider the case `cons X W ih`.

Introduce `hW`. Establish `hW' : ∀ Y ∈ W, InLieHpk k r Y` using `fun Y hY => hW Y (List.mem_cons_of_mem X hY)`. Establish `hX : InLieHpk k r X` using `hW X (List.mem_cons_self ..)`. Use `show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (a • v)) = a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)`. Rewrite using `[ih hW']`.

Establish `hv'` using `dsigW_mem hD W hW' v hv`. Establish `hd` using `((hD X hX).1 _ hv').2.const_smul a`. Establish `hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (a • dsigW (k` using `k) (r := r) R.σ W v)) (a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)) 0 := by`. Simplify `hd` using `only [map_smul, Pi.smul_def]`. Conclude with `hd'.deriv`.
-/
theorem dsigW_smul {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (a : ℂ) (v : R.H) (hv : v ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (a • v) = a • dsigW (k := k) (r := r) R.σ W v := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (a • v)) =
      a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hd := ((hD X hX).1 _ hv').2.const_smul a
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (a • dsigW (k := k) (r := r) R.σ W v))
        (a • dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v)) 0 := by
      simpa only [map_smul, Pi.smul_def] using hd
    exact hd'.deriv

/- English proof (translation)
Use `revert hW`. Proceed by induction on `W with`. Consider the case `nil => intro _`. Both sides reduce to the same expression. Consider the case `cons X W ih`.

Introduce `hW`. Establish `hW' : ∀ Y ∈ W, InLieHpk k r Y` using `fun Y hY => hW Y (List.mem_cons_of_mem X hY)`. Establish `hX : InLieHpk k r X` using `hW X (List.mem_cons_self ..)`. Use `show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (v + w)) = dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) + dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)`. Rewrite using `[ih hW']`.

Establish `hv'` using `dsigW_mem hD W hW' v hv`. Establish `hw'` using `dsigW_mem hD W hW' w hw`. Establish `hd` using `((hD X hX).1 _ hv').2.add ((hD X hX).1 _ hw').2`. Establish `hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) (dsigW (k` using `k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w)) (dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) + dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)) 0 := by`. Simplify `hd` using `only [map_add, Pi.add_def]`.

Conclude with `hd'.deriv`.
-/
theorem dsigW_add {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    (v : R.H) (hv : v ∈ R.sm) (w : R.H) (hw : w ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (v + w) =
      dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w := by
  revert hW
  induction W with
  | nil => intro _; rfl
  | cons X W ih =>
    intro hW
    have hW' : ∀ Y ∈ W, InLieHpk k r Y := fun Y hY => hW Y (List.mem_cons_of_mem X hY)
    have hX : InLieHpk k r X := hW X (List.mem_cons_self ..)
    show dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W (v + w)) =
      dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
        dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)
    rw [ih hW']
    have hv' := dsigW_mem hD W hW' v hv
    have hw' := dsigW_mem hD W hW' w hw
    have hd := ((hD X hX).1 _ hv').2.add ((hD X hX).1 _ hw').2
    have hd' : HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X))
        (dsigW (k := k) (r := r) R.σ W v + dsigW (k := k) (r := r) R.σ W w))
        (dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W v) +
          dsig (k := k) (r := r) R.σ X (dsigW (k := k) (r := r) R.σ W w)) 0 := by
      simpa only [map_add, Pi.add_def] using hd
    exact hd'.deriv

/- English proof (translation)
Establish `hmem : ∀ x, dsigW (k` using `k) (r := r) R.σ W (f x) ∈ R.smSub := fun x => dsigW_mem hD W hW _ (hf x)`. Establish `hcl : ((R.smSub.topologicalClosure : Submodule ℂ R.H) : Set R.H) = closure R.sm` using `Submodule.topologicalClosure_coe _`. Establish `hy : (∫ x, dsigW (k` using `k) (r := r) R.σ W (f x) ∂μ) ∈ R.smSub.topologicalClosure := by`. Rewrite using `[← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]`. Introduce `z hz`.

Rewrite using `[← integral_inner hi']`. Use `integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `Submodule.inner_left_of_mem_orthogonal (hmem x) hz`. Establish `hd : dsigW (k` using `k) (r := r) R.σ W (∫ x, f x ∂μ) ∈ R.smSub := dsigW_mem hD W hW _ hu`. Use `sub_eq_zero.mp (eq_zero_of_closure ?_ ?_)` and prove the remaining obligations.

Rewrite using `[← hcl]`. Conclude with `Submodule.sub_mem _ (R.smSub.le_topologicalClosure hd) hy`. Introduce `w hw`. Take `⟨w', hw'⟩` from `dsigW_adjoint hD W hW w hw`. Rewrite using `[inner_sub_right, hw' _ hu, ← integral_inner hi, ← integral_inner hi', sub_eq_zero]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `(hw' _ (hf x)).symm`.
-/
theorem dsigW_integral {R : Rep k r} (hD : DerFacts R) (W : List (Mx k r)) (hW : ∀ X ∈ W, InLieHpk k r X)
    {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → R.H) (hf : ∀ x, f x ∈ R.sm)
    (hi : Integrable f μ) (hi' : Integrable (fun x => dsigW (k := k) (r := r) R.σ W (f x)) μ)
    (hu : (∫ x, f x ∂μ) ∈ R.sm) :
    dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) = ∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ := by
  have hmem : ∀ x, dsigW (k := k) (r := r) R.σ W (f x) ∈ R.smSub := fun x => dsigW_mem hD W hW _ (hf x)
  have hcl : ((R.smSub.topologicalClosure : Submodule ℂ R.H) : Set R.H) = closure R.sm :=
    Submodule.topologicalClosure_coe _
  have hy : (∫ x, dsigW (k := k) (r := r) R.σ W (f x) ∂μ) ∈ R.smSub.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro z hz
    rw [← integral_inner hi']
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    exact Submodule.inner_left_of_mem_orthogonal (hmem x) hz
  have hd : dsigW (k := k) (r := r) R.σ W (∫ x, f x ∂μ) ∈ R.smSub := dsigW_mem hD W hW _ hu
  refine sub_eq_zero.mp (eq_zero_of_closure ?_ ?_)
  · rw [← hcl]
    exact Submodule.sub_mem _ (R.smSub.le_topologicalClosure hd) hy
  · intro w hw
    obtain ⟨w', hw'⟩ := dsigW_adjoint hD W hW w hw
    rw [inner_sub_right, hw' _ hu, ← integral_inner hi, ← integral_inner hi', sub_eq_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (hw' _ (hf x)).symm

end GlobalTheory.CWIntegral

namespace GlobalTheory

open PI.UpqRep GlobalTheory.CWDeriv GlobalTheory.CWIntegral

/- English proof (translation)
Introduce `hKS k r ε mu R hR V indexVFirst indexVSecond indexVThird indexVFourth Bm hadd hsmul hcw X iX1 iX2 iX3 iX4 iX5 μ iμ κ p hκ hκG hp v hv hu`. Establish `hD : DerFacts R` using `fun Y hY => ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).2.2.2.2⟩`. Establish `hσ : ∀ x, R.σ (κ x) v ∈ R.sm` using `fun x => (rep_basic_of_isDS hKS k r ε mu R hR).2.2.2.1 _ (hκG x) v hv`. Establish `hf : ∀ x, p x • R.σ (κ x) v ∈ R.sm` using `fun x => R.smSub.smul_mem (p x) (hσ x)`. Establish `hint : ∀ {E : Type} [NormedAddCommGroup E] (g : X → E), Continuous g → Integrable g μ` using `fun g hg => hg.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (Set.subset_univ _))`.

Establish `hcW : ∀ W : List (Mx k r), (∀ Y ∈ W, InLieHpk k r Y) → Continuous (fun x => PI.UpqRep.dsigW (k` using `k) (r := r) R.σ W (R.σ (κ x) v)) := fun W hW => (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW)).comp_continuous hκ hκG`. Establish `hBc : Continuous (fun x => Bm (R.σ (κ x) v))` using `(cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1.comp_continuous hκ hκG`. Take `⟨C, Ws, hWs, hB⟩` from `hcw`. Establish `hWi : ∀ i : Fin Ws.length, ∀ Y ∈ Ws.get i, InLieHpk k r Y` using `fun i => hWs _ (List.get_mem Ws i)`. Set `T : R.smSub →ₗ[ℂ] (Fin Ws.length → R.H)` to `linOn R (fun u i => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) u) (fun a ha b hb => funext fun i => dsigW_add hD _ (hWi i) a ha b hb) (fun c a ha => funext fun i => dsigW_smul hD _ (hWi i) c a ha)`.

Use `ext_inner_left ℂ (fun e => ?_)` and prove the remaining obligations. Set `φ : R.smSub →ₗ[ℂ] ℂ` to `(innerSL ℂ e : V →L[ℂ] ℂ).toLinearMap.comp (linOn R Bm hadd hsmul)`. Establish `hφ : ∀ s, φ s = ⟪e, Bm s⟫_ℂ` using `fun s => rfl`. Establish `hbound : ∀ s, ‖φ s‖ ≤ (‖e‖ * (|C| * Ws.length)) * ‖T s‖`. Introduce `s`.

Establish `h1 : ‖Bm s‖ ≤ C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k` using `k) (r := r) R.σ w s‖).sum := hB s s.2`. Establish `h2 : (Ws.map fun w => ‖PI.UpqRep.dsigW (k` using `k) (r := r) R.σ w s‖).sum ≤ Ws.length * ‖T s‖ := by`. Establish `h3` using `List.sum_le_card_nsmul (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖) ‖T s‖ (by`. Introduce `y hy`. Take `⟨w, hw, rfl⟩` from `List.mem_map.mp hy`.

Take `⟨i, rfl⟩` from `List.mem_iff_get.mp hw`. Conclude with `norm_le_pi_norm (T s) i)`. Rewrite `h3` using `[List.length_map, nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `h0 : 0 ≤ (Ws.map fun w => ‖PI.UpqRep.dsigW (k` using `k) (r := r) R.σ w s‖).sum := List.sum_nonneg (fun y hy => by`. Take `⟨w, -, rfl⟩` from `List.mem_map.mp hy`.

Conclude with `norm_nonneg _)`. Establish `h4 : ‖Bm s‖ ≤ |C| * (Ws.length * ‖T s‖)` using `h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))`. Rewrite using `[hφ]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨Λ, hΛ⟩` from `exists_functional T φ _ hbound`.

Set `F : X → (Fin Ws.length → R.H)` to `fun x i => p x • PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (R.σ (κ x) v)`. Establish `hFi : Integrable F μ` using `hint F (continuous_pi fun i => hp.smul (hcW _ (hWi i)))`. Establish `hTu : T ⟨_, hu⟩ = ∫ x, F x ∂μ`. Use function extensionality and compare the values at `i`. Establish `hpi` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Ws.length => R.H) i).integral_comp_comm hFi`.

Simplify using `only [ContinuousLinearMap.proj_apply] at hpi`. Rewrite using `[← hpi]`. Use `show PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, F x i ∂μ`. Establish `hi0 : Integrable (fun x => p x • R.σ (κ x) v) μ` using `hint _ (hp.smul (hcW [] (by simp)))`. Establish `hi1 : Integrable (fun x => PI.UpqRep.dsigW (k` using `k) (r := r) R.σ (Ws.get i) (p x • R.σ (κ x) v)) μ := (hint _ (hp.smul (hcW _ (hWi i)))).congr (Filter.Eventually.of_forall fun x => (dsigW_smul hD _ (hWi i) (p x) _ (hσ x)).symm)`.

Rewrite using `[dsigW_integral hD _ (hWi i) μ _ hf hi0 hi1 hu]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun x => dsigW_smul hD _ (hWi i) (p x) _ (hσ x))`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hF : F x = p x • T ⟨_, hσ x⟩` using `rfl`.

Use `show Λ (F x) = ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ`. Rewrite using `[hF, map_smul, hΛ, hφ, inner_smul_right, smul_eq_mul]`. Use `_ = ⟪e, ∫ x, p x • Bm (R.σ (κ x) v) ∂μ⟫_ℂ := integral_inner (hint _ (hp.smul hBc)) e`.
-/
theorem cwCont_integral_comm : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  intro hKS k r ε mu R hR V indexVFirst indexVSecond indexVThird indexVFourth Bm hadd hsmul hcw X iX1 iX2 iX3 iX4 iX5 μ iμ κ p hκ hκG hp v hv hu
  have hD : DerFacts R := fun Y hY =>
    ⟨(GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).1, (GlobalTheory.T.derivedAction_discreteSeries_properties hKS k r ε mu R hR Y hY).2.2.2.2⟩
  have hσ : ∀ x, R.σ (κ x) v ∈ R.sm := fun x => (rep_basic_of_isDS hKS k r ε mu R hR).2.2.2.1 _ (hκG x) v hv
  have hf : ∀ x, p x • R.σ (κ x) v ∈ R.sm := fun x => R.smSub.smul_mem (p x) (hσ x)
  have hint : ∀ {E : Type} [NormedAddCommGroup E] (g : X → E), Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport g) (Set.subset_univ _))
  have hcW : ∀ W : List (Mx k r), (∀ Y ∈ W, InLieHpk k r Y) →
      Continuous (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ W (R.σ (κ x) v)) := fun W hW =>
    (smoothOnH_continuousOn (dsigW_orbit_smooth hR hD hv W hW)).comp_continuous hκ hκG
  have hBc : Continuous (fun x => Bm (R.σ (κ x) v)) :=
    (cwCont_continuousOn_hasDerivAt hKS k r ε mu R hR V Bm hadd hsmul hcw v hv).1.comp_continuous hκ hκG
  obtain ⟨C, Ws, hWs, hB⟩ := hcw
  have hWi : ∀ i : Fin Ws.length, ∀ Y ∈ Ws.get i, InLieHpk k r Y := fun i => hWs _ (List.get_mem Ws i)
  let T : R.smSub →ₗ[ℂ] (Fin Ws.length → R.H) :=
    linOn R (fun u i => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) u)
      (fun a ha b hb => funext fun i => dsigW_add hD _ (hWi i) a ha b hb)
      (fun c a ha => funext fun i => dsigW_smul hD _ (hWi i) c a ha)
  refine ext_inner_left ℂ (fun e => ?_)
  let φ : R.smSub →ₗ[ℂ] ℂ := (innerSL ℂ e : V →L[ℂ] ℂ).toLinearMap.comp (linOn R Bm hadd hsmul)
  have hφ : ∀ s, φ s = ⟪e, Bm s⟫_ℂ := fun s => rfl
  have hbound : ∀ s, ‖φ s‖ ≤ (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by
    intro s
    have h1 : ‖Bm s‖ ≤ C * (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum := hB s s.2
    have h2 : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum ≤ Ws.length * ‖T s‖ := by
      have h3 := List.sum_le_card_nsmul (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖) ‖T s‖
        (by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
          exact norm_le_pi_norm (T s) i)
      rwa [List.length_map, nsmul_eq_mul] at h3
    have h0 : 0 ≤ (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ w s‖).sum :=
      List.sum_nonneg (fun y hy => by
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hy
        exact norm_nonneg _)
    have h4 : ‖Bm s‖ ≤ |C| * (Ws.length * ‖T s‖) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) h0).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    rw [hφ]
    calc ‖⟪e, Bm s⟫_ℂ‖ ≤ ‖e‖ * ‖Bm s‖ := norm_inner_le_norm _ _
      _ ≤ ‖e‖ * (|C| * (Ws.length * ‖T s‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg e)
      _ = (‖e‖ * (|C| * Ws.length)) * ‖T s‖ := by ring
  obtain ⟨Λ, hΛ⟩ := exists_functional T φ _ hbound
  let F : X → (Fin Ws.length → R.H) := fun x i =>
    p x • PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (R.σ (κ x) v)
  have hFi : Integrable F μ := hint F (continuous_pi fun i => hp.smul (hcW _ (hWi i)))
  have hTu : T ⟨_, hu⟩ = ∫ x, F x ∂μ := by
    funext i
    have hpi := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin Ws.length => R.H) i).integral_comp_comm hFi
    simp only [ContinuousLinearMap.proj_apply] at hpi
    rw [← hpi]
    show PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, F x i ∂μ
    have hi0 : Integrable (fun x => p x • R.σ (κ x) v) μ := hint _ (hp.smul (hcW [] (by simp)))
    have hi1 : Integrable (fun x => PI.UpqRep.dsigW (k := k) (r := r) R.σ (Ws.get i) (p x • R.σ (κ x) v)) μ :=
      (hint _ (hp.smul (hcW _ (hWi i)))).congr
        (Filter.Eventually.of_forall fun x => (dsigW_smul hD _ (hWi i) (p x) _ (hσ x)).symm)
    rw [dsigW_integral hD _ (hWi i) μ _ hf hi0 hi1 hu]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => dsigW_smul hD _ (hWi i) (p x) _ (hσ x))
  calc ⟪e, Bm (∫ x, p x • R.σ (κ x) v ∂μ)⟫_ℂ = φ ⟨_, hu⟩ := (hφ ⟨_, hu⟩).symm
    _ = Λ (T ⟨_, hu⟩) := (hΛ ⟨_, hu⟩).symm
    _ = Λ (∫ x, F x ∂μ) := by rw [hTu]
    _ = ∫ x, Λ (F x) ∂μ := (Λ.integral_comp_comm hFi).symm
    _ = ∫ x, ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hF : F x = p x • T ⟨_, hσ x⟩ := rfl
        show Λ (F x) = ⟪e, p x • Bm (R.σ (κ x) v)⟫_ℂ
        rw [hF, map_smul, hΛ, hφ, inner_smul_right, smul_eq_mul]
    _ = ⟪e, ∫ x, p x • Bm (R.σ (κ x) v) ∂μ⟫_ℂ := integral_inner (hint _ (hp.smul hBc)) e

end GlobalTheory

end
