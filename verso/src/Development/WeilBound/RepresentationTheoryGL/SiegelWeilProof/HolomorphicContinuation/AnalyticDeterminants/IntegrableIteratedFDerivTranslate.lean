import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IteratedFDerivMulConstOf

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Establish `h` using `continuousOn_iteratedFDeriv_translate F U hU hF Kg ι hι c hc N`. Establish `hg : Continuous (fun k : Kg => (k, x))` using `continuous_id.prodMk continuous_const`. Establish `hm : ∀ k, (k, x) ∈ (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U} : Set (Kg × M2 n))` using `fun k => ⟨Set.mem_univ _, hx⟩`. Establish `h2 : Continuous (fun k : Kg => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x)` using `h.comp_continuous hg hm`. Conclude with `integrable_of_continuous_K μ ((continuous_eval_const w).comp h2)`.
-/
theorem integrable_iteratedFDeriv_translate (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι) (c : Kg → ℂ) (hc : Continuous c)
    (N : ℕ) (x : M2 n) (hx : ∀ k, ι k * x ∈ U) (w : Fin N → M2 n) :
    Integrable (fun k => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x w) μ := by
  have h := continuousOn_iteratedFDeriv_translate F U hU hF Kg ι hι c hc N
  have hg : Continuous (fun k : Kg => (k, x)) := continuous_id.prodMk continuous_const
  have hm : ∀ k, (k, x) ∈ (Set.univ ×ˢ {x | ∀ k, ι k * x ∈ U} : Set (Kg × M2 n)) :=
    fun k => ⟨Set.mem_univ _, hx⟩
  have h2 : Continuous (fun k : Kg => iteratedFDeriv ℂ N (fun y => F (ι k * y) * c k) x) :=
    h.comp_continuous hg hm
  exact integrable_of_continuous_K μ ((continuous_eval_const w).comp h2)

/- English proof (translation)
Use `set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ`. Establish `hΩo : IsOpen Ω` using `isOpen_domK Kg ι hι`. Establish `hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => F (ι k * x) * c k) Ω` using `fun k => (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const`. Establish `hH` using `hHI n Kg μ Ω (fun k x => F (ι k * x) * c k) hΩo (fun N => continuousOn_iteratedFDeriv_translate F (Dom n) isOpen_dom hF Kg ι hι c hc N) hsm`. Establish `hgΩ : g ∈ Ω` using `hg`.

Establish `hAv : ContDiffOn ℂ ∞ (fun x => ∫ k, F (ι k * x) * c k ∂μ) Ω` using `hH.1`. Establish `key : ∀ (N : ℕ) (v : Fin N → M2 n), iteratedFDeriv ℂ N (fun x => ∫ k, F (ι k * x) * c k ∂μ) g v = ∫ k, iteratedFDeriv ℂ N (fun x => F (ι k * x) * c k) g v ∂μ` using `fun N v => hH.2 N g v hgΩ`. Establish `e0 : (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) = fun T => detD (fun S => (fun x => ∫ k, F (ι k * x) * c k ∂μ) (g + LA g T + LB g S))` using `rfl`. Establish `hFc : ∀ k, ContDiffOn ℂ ∞ (fun y => F y * c k) (Dom n)` using `fun k => hF.mul contDiffOn_const`. Establish `hk : ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k = ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fu …`.

Introduce `k`. Rewrite using `[← detD_detD_mul_const F (Dom n) isOpen_dom hF (ι k * g) (hg k) (LA (ι k * g)) (LB (ι k * g)) (c k), detD_detD_comp (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k * g) (hg k) _ _]`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[iteratedFDeriv_left_mul (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k) g (hg k), fin_append_mul]`.

Simplify using `only [hLA, hLB]`. Establish `hint : ∀ (σ : Equiv.Perm ιA) (τ : Equiv.Perm ιB), Integrable (fun k => iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1)) (fun i => LB …` using `fun σ τ => integrable_iteratedFDeriv_translate F (Dom n) isOpen_dom hF μ ι hι c hc _ g hg _`. Rewrite using `[e0, detD_detD_comp _ Ω hΩo hAv g hgΩ (LA g) (LB g), integral_congr_ae (Filter.Eventually.of_forall hk)]`. Simplify using `only [key]`. Use `symm`.

Rewrite using `[integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint σ τ).const_mul _))]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ (fun τ _ => (hint σ τ).const_mul _)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`.
-/
theorem spherical_detD (hHI : HolInt) (F : M2 n → ℂ) (hF : ContDiffOn ℂ ∞ F (Dom n))
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] [IsFiniteMeasureOnCompacts μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (LA : M2 n → Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : M2 n → Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hLA : ∀ M x T, LA (M * x) T = M * LA x T) (hLB : ∀ M x S, LB (M * x) S = M * LB x S)
    (g : M2 n) (hg : ∀ k, ι k * g ∈ Dom n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ)) =
      ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k ∂μ := by
  classical
  set Ω : Set (M2 n) := {x | ∀ k, ι k * x ∈ Dom n} with hΩ
  have hΩo : IsOpen Ω := isOpen_domK Kg ι hι
  have hsm : ∀ k, ContDiffOn ℂ ∞ (fun x => F (ι k * x) * c k) Ω := fun k =>
    (hF.comp (contDiff_mulLeft (ι k)).contDiffOn (fun x (hx : x ∈ Ω) => hx k)).mul contDiffOn_const
  have hH := hHI n Kg μ Ω (fun k x => F (ι k * x) * c k) hΩo
    (fun N => continuousOn_iteratedFDeriv_translate F (Dom n) isOpen_dom hF Kg ι hι c hc N) hsm
  have hgΩ : g ∈ Ω := hg
  have hAv : ContDiffOn ℂ ∞ (fun x => ∫ k, F (ι k * x) * c k ∂μ) Ω := hH.1
  have key : ∀ (N : ℕ) (v : Fin N → M2 n), iteratedFDeriv ℂ N (fun x => ∫ k, F (ι k * x) * c k ∂μ) g v =
      ∫ k, iteratedFDeriv ℂ N (fun x => F (ι k * x) * c k) g v ∂μ := fun N v => hH.2 N g v hgΩ
  have e0 : (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => ∫ k, F (ι k * (g + LA g T + LB g S)) * c k ∂μ))
      = fun T => detD (fun S => (fun x => ∫ k, F (ι k * x) * c k ∂μ) (g + LA g T + LB g S)) := rfl
  have hFc : ∀ k, ContDiffOn ℂ ∞ (fun y => F y * c k) (Dom n) := fun k => hF.mul contDiffOn_const
  have hk : ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
      F (ι k * g + LA (ι k * g) T + LB (ι k * g) S))) * c k =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro k
    rw [← detD_detD_mul_const F (Dom n) isOpen_dom hF (ι k * g) (hg k) (LA (ι k * g)) (LB (ι k * g)) (c k),
      detD_detD_comp (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k * g) (hg k) _ _]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    rw [iteratedFDeriv_left_mul (fun y => F y * c k) (Dom n) isOpen_dom (hFc k) (ι k) g (hg k), fin_append_mul]
    simp only [hLA, hLB]
  have hint : ∀ (σ : Equiv.Perm ιA) (τ : Equiv.Perm ιB), Integrable (fun k =>
      iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) (fun x => F (ι k * x) * c k) g
          (Fin.append (fun i => LA g (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB g (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1)))) μ :=
    fun σ τ => integrable_iteratedFDeriv_translate F (Dom n) isOpen_dom hF μ ι hι c hc _ g hg _
  rw [e0, detD_detD_comp _ Ω hΩo hAv g hgΩ (LA g) (LB g), integral_congr_ae (Filter.Eventually.of_forall hk)]
  simp only [key]
  symm
  rw [integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint σ τ).const_mul _))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint σ τ).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul]

/- English proof (translation)
Establish `hιK : ∀ k, InK (ι k)` using `fun k => (hK (ι k)).2 ⟨k, rfl⟩`. Establish `hιDom : ∀ k, ι k ∈ Dom n` using `fun k => gset_sub_dom (hιK k).1`. Use `set N := Fintype.card ιA + Fintype.card ιB with hN`. Set `W : Equiv.Perm ιA → Equiv.Perm ιB → Fin N → M2 n` to `fun σ τ => Fin.append (fun i => WA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1)) (fun i => WB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))`. Establish `hWW : ∀ σ τ a b, W σ τ a * W σ τ b = 0`.

Introduce `σ τ a b`. Establish `hAA : ∀ T T' : Matrix ιA ιA ℂ, WA T * WA T' = 0` using `fun T T' => by`. Simplify `hW T T' 0 0` using `only [map_zero, add_zero]`. Establish `hAB : ∀ (T : Matrix ιA ιA ℂ) (S' : Matrix ιB ιB ℂ), WA T * WB S' = 0` using `fun T S' => by`. Simplify `hW T 0 0 S'` using `only [map_zero, add_zero, zero_add]`.

Establish `hBA : ∀ (S : Matrix ιB ιB ℂ) (T' : Matrix ιA ιA ℂ), WB S * WA T' = 0` using `fun S T' => by`. Simplify `hW 0 T' S 0` using `only [map_zero, add_zero, zero_add]`. Establish `hBB : ∀ S S' : Matrix ιB ιB ℂ, WB S * WB S' = 0` using `fun S S' => by`. Simplify `hW 0 0 S S'` using `only [map_zero, zero_add]`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;>`.

Simplify using `only [W, Fin.append_left, Fin.append_right]`. Conclude with `hAA _ _`. Conclude with `hAB _ _`. Conclude with `hBA _ _`. Conclude with `hBB _ _`.

Establish `expand : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k + ι k * WA T + ι k * WB S))) = ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ N F (ι k …`. Introduce `F hF k`. Establish `e` using `detD_detD_comp F (Dom n) isOpen_dom hF (ι k) (hιDom k) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WA) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WB)`. Use `e.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_)` and prove the remaining obligations. Use `congr 2`.

Rewrite using `[fin_append_mul]`. Both sides reduce to the same expression. Establish `hcontD : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ σ τ, Continuous (fun k => iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i))`. Introduce `F hF σ τ`. Establish `h1 : ContinuousOn (iteratedFDeriv ℂ N F) (Dom n)` using `(hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) isOpen_dom.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen N isOpen_dom hx).symm)`.

Establish `h2 : Continuous (fun k => iteratedFDeriv ℂ N F (ι k))` using `h1.comp_continuous hι hιDom`. Establish `h3 : Continuous (fun k => (fun i => ι k * W σ τ i : Fin N → M2 n))` using `continuous_pi fun i => hι.mul continuous_const`. Conclude with `h2.eval h3`. Establish `hc1 : Continuous fun k => F1 (ι k)` using `hF1.continuousOn.comp_continuous hι hιDom`. Establish `hc2 : Continuous fun k => F2 (ι k)` using `hF2.continuousOn.comp_continuous hι hιDom`.

Establish `hint1 : ∀ σ τ, Integrable (fun k => iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) μ` using `fun σ τ => integrable_of_continuous_K μ ((hcontD F1 hF1 σ τ).mul hc2)`. Establish `hint2 : ∀ σ τ, Integrable (fun k => F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) μ` using `fun σ τ => integrable_of_continuous_K μ (hc1.mul (hcontD F2 hF2 σ τ))`. Establish `eL : (fun k => detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k)) = fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * (iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W …`. Use function extensionality and compare the values at `k`. Rewrite using `[expand F1 hF1 k, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `eR : (fun k => F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S)))) = fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) * (F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i …`.

Use function extensionality and compare the values at `k`. Rewrite using `[expand F2 hF2 k, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eL, eR, integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _)), integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _)), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _), integral_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_const_mul, integral_const_mul, transpose hI F1 F2 χ1 χ2 hF1 hF2 h1 h2 h12 Kg μ ι hι hK N (W σ τ) (hWW σ τ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem transpose_detD (hI : InfInv) (F1 F2 : M2 n → ℂ) (χ1 χ2 : M2 n → ℂ) (hF1 : ContDiffOn ℂ ∞ F1 (Dom n))
    (hF2 : ContDiffOn ℂ ∞ F2 (Dom n)) (h1 : ∀ P x, InP P → x ∈ Dom n → F1 (P * x) = χ1 P * F1 x)
    (h2 : ∀ P x, InP P → x ∈ Dom n → F2 (P * x) = χ2 P * F2 x)
    (h12 : ∀ P, InP P → χ1 P * χ2 P = ((‖(P.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ))
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (WA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (WB : Matrix ιB ιB ℂ →L[ℂ] M2 n)
    (hW : ∀ (T T' : Matrix ιA ιA ℂ) (S S' : Matrix ιB ιB ℂ), (WA T + WB S) * (WA T' + WB S') = 0) :
    ∫ k, detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k) ∂μ =
      (-1) ^ (Fintype.card ιA + Fintype.card ιB) * ∫ k, F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ =>
        detD (fun S : Matrix ιB ιB ℂ => F2 (ι k + ι k * WA T + ι k * WB S))) ∂μ := by
  classical
  have hιK : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hιDom : ∀ k, ι k ∈ Dom n := fun k => gset_sub_dom (hιK k).1
  set N := Fintype.card ιA + Fintype.card ιB with hN
  let W : Equiv.Perm ιA → Equiv.Perm ιB → Fin N → M2 n := fun σ τ =>
    Fin.append (fun i => WA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
      (fun i => WB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))
  have hWW : ∀ σ τ a b, W σ τ a * W σ τ b = 0 := by
    intro σ τ a b
    have hAA : ∀ T T' : Matrix ιA ιA ℂ, WA T * WA T' = 0 := fun T T' => by
      simpa only [map_zero, add_zero] using hW T T' 0 0
    have hAB : ∀ (T : Matrix ιA ιA ℂ) (S' : Matrix ιB ιB ℂ), WA T * WB S' = 0 := fun T S' => by
      simpa only [map_zero, add_zero, zero_add] using hW T 0 0 S'
    have hBA : ∀ (S : Matrix ιB ιB ℂ) (T' : Matrix ιA ιA ℂ), WB S * WA T' = 0 := fun S T' => by
      simpa only [map_zero, add_zero, zero_add] using hW 0 T' S 0
    have hBB : ∀ S S' : Matrix ιB ιB ℂ, WB S * WB S' = 0 := fun S S' => by
      simpa only [map_zero, zero_add] using hW 0 0 S S'
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun i' => ?_) (fun i' => ?_) b <;>
      simp only [W, Fin.append_left, Fin.append_right]
    · exact hAA _ _
    · exact hAB _ _
    · exact hBA _ _
    · exact hBB _ _
  have expand : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ k,
      detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (ι k + ι k * WA T + ι k * WB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i) := by
    intro F hF k
    have e := detD_detD_comp F (Dom n) isOpen_dom hF (ι k) (hιDom k)
      ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WA) ((LinearMap.mulLeft ℂ (ι k)).toContinuousLinearMap.comp WB)
    refine e.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_)
    congr 2
    rw [fin_append_mul]
    rfl
  have hcontD : ∀ (F : M2 n → ℂ), ContDiffOn ℂ ∞ F (Dom n) → ∀ σ τ,
      Continuous (fun k => iteratedFDeriv ℂ N F (ι k) (fun i => ι k * W σ τ i)) := by
    intro F hF σ τ
    have h1 : ContinuousOn (iteratedFDeriv ℂ N F) (Dom n) :=
      (hF.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) isOpen_dom.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen N isOpen_dom hx).symm)
    have h2 : Continuous (fun k => iteratedFDeriv ℂ N F (ι k)) := h1.comp_continuous hι hιDom
    have h3 : Continuous (fun k => (fun i => ι k * W σ τ i : Fin N → M2 n)) :=
      continuous_pi fun i => hι.mul continuous_const
    exact h2.eval h3
  have hc1 : Continuous fun k => F1 (ι k) := hF1.continuousOn.comp_continuous hι hιDom
  have hc2 : Continuous fun k => F2 (ι k) := hF2.continuousOn.comp_continuous hι hιDom
  have hint1 : ∀ σ τ, Integrable (fun k => iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) μ :=
    fun σ τ => integrable_of_continuous_K μ ((hcontD F1 hF1 σ τ).mul hc2)
  have hint2 : ∀ σ τ, Integrable (fun k => F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) μ :=
    fun σ τ => integrable_of_continuous_K μ (hc1.mul (hcontD F2 hF2 σ τ))
  have eL : (fun k => detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F1 (ι k + ι k * WA T + ι k * WB S))) * F2 (ι k)) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (iteratedFDeriv ℂ N F1 (ι k) (fun i => ι k * W σ τ i) * F2 (ι k)) := by
    funext k; rw [expand F1 hF1 k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have eR : (fun k => F1 (ι k) * detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ =>
        F2 (ι k + ι k * WA T + ι k * WB S)))) =
      fun k => ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        (F1 (ι k) * iteratedFDeriv ℂ N F2 (ι k) (fun i => ι k * W σ τ i)) := by
    funext k; rw [expand F2 hF2 k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [eL, eR, integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _)),
    integral_finset_sum _ (fun σ _ => integrable_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ (fun τ _ => (hint1 σ τ).const_mul _),
    integral_finset_sum _ (fun τ _ => (hint2 σ τ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_const_mul,
    transpose hI F1 F2 χ1 χ2 hF1 hF2 h1 h2 h12 Kg μ ι hι hK N (W σ τ) (hWW σ τ)]
  ring

end PositivityTheory.Rg.Sw.LVs
