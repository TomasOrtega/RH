import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowLe

set_option synthInstance.maxSize 1000

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic.GJMatrix GlobalTheory.ThetaPoisson

open scoped Classical

namespace GlobalTheory.SchwartzBruhatMoments

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

/- English proof (translation)
Rewrite using `[← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem pInfPi_eq (x : Fin m → Ad E) :
    (fun i => pInf E (x i)) = (toMixedPi E m).symm (infPartPi x) := by
  rw [← toMixedPi_pInf, ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le`. Consider the case `exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le`. Consider the case `(apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le ..)`.
-/
theorem one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  first
  | exact @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le
  | (apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneAddPowBound.one_add_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneAddPowBound.one_add_pow_le ..)

/- English proof (translation)
Use `set S := (toMixedPi E m).symm`. Use `set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖`. Establish `hC : 0 ≤ C` using `norm_nonneg _`. Establish `hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖)) (mixedMeasurePi E)` using `((φ.integrable (μ := mixedMeasurePi E)).norm.add (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _`. Use `hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Conclude with `(φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable`. Establish `h1 : ‖S u‖ ≤ C * ‖u‖` using `(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u`. Establish `h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖)` using `by nlinarith [norm_nonneg u, norm_nonneg (S u)]`. Establish `h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_arch (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ) (k : ℕ) :
    Integrable (fun u => ‖φ u‖ * (1 + ‖(toMixedPi E m).symm u‖) ^ k) (mixedMeasurePi E) := by
  set S := (toMixedPi E m).symm
  set C := ‖(S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E))‖
  have hC : 0 ≤ C := norm_nonneg _
  have hint : Integrable (fun u => ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖))
      (mixedMeasurePi E) :=
    ((φ.integrable (μ := mixedMeasurePi E)).norm.add
      (φ.integrable_pow_mul (mixedMeasurePi E) k)).const_mul _
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (φ.continuous.norm.mul ((continuous_const.add S.continuous.norm).pow k)).aestronglyMeasurable
  · have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin m → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin m → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ k ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) := by
      calc (1 + ‖S u‖) ^ k ≤ ((1 + C) * (1 + ‖u‖)) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = (1 + C) ^ k * (1 + ‖u‖) ^ k := mul_pow _ _ _
        _ ≤ (1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le (norm_nonneg u) k) (by positivity)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖φ u‖ * (1 + ‖S u‖) ^ k ≤ ‖φ u‖ * ((1 + C) ^ k * (2 ^ k * (1 + ‖u‖ ^ k))) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = ((1 + C) ^ k * 2 ^ k) * (‖φ u‖ + ‖u‖ ^ k * ‖φ u‖) := by ring

/- English proof (translation)
Establish `h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) = (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) => (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, splitEquivPi_apply]`. Rewrite using `[pInfPi_eq]`. Rewrite using `[h]`.

Conclude with `((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable`.
-/
theorem aestronglyMeasurable_weight (k : ℕ) :
    AEStronglyMeasurable (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply]
    rw [pInfPi_eq]
  rw [h]
  exact ((((continuous_const.add (toMixedPi E m).symm.continuous.norm).pow k).measurable.comp
    measurable_fst).comp (splitEquivPi E (Fin m)).measurable).aestronglyMeasurable

/- English proof (translation)
Establish `h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) = (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) => (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]`. Rewrite using `[pInfPi_eq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]`. Conclude with `(integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm`.
-/
theorem integrable_tensor (φ : SchwartzMap (Fin m → mixedEmbedding.mixedSpace E) ℂ)
    {g : (Fin m → Af E) → ℂ} (hg : g ∈ finiteSchwartzBruhatPi E) (k : ℕ) :
    Integrable (fun x => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (adeleMeasurePi E) := by
  have h : (fun x : Fin m → Ad E => ‖schwartzBruhatTensorPi φ g x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k) =
      (fun p : (Fin m → mixedEmbedding.mixedSpace E) × (Fin m → Af E) =>
        (‖φ p.1‖ * (1 + ‖(toMixedPi E m).symm p.1‖) ^ k) * ‖g p.2‖) ∘ splitEquivPi E (Fin m) := by
    funext x
    simp only [Function.comp_apply, splitEquivPi_apply, schwartzBruhatTensorPi, norm_mul]
    rw [pInfPi_eq]
    ring
  rw [h, measurePreserving_splitEquivPi.integrable_comp_emb (splitEquivPi E (Fin m)).measurableEmbedding]
  exact (integrable_arch φ k).mul_prod (integrable_of_mem_finiteSchwartzBruhatPi hg).norm

/- English proof (translation)
Introduce `E _ _ _ m F hF`. Use `⟨?_, fun k => ?_⟩` and prove the remaining obligations. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`.

Use `⟨tsupport g, hg.2, fun x hx => ?_⟩` and prove the remaining obligations. Establish `e : (fun i => pFin E (x i)) = finPartPi x` using `rfl`. Rewrite using `[e]`. Apply `subset_tsupport` to reduce the goal to its premises. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Simplify using `only [schwartzBruhatTensorPi, h0, mul_zero]`. Consider the case `zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩`. Consider the case `add G H _ _ hG hH`. Take `⟨L1, h1, hL1⟩` from `hG`.

Take `⟨L2, h2, hL2⟩` from `hH`. Use `⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hGx : G x = 0`. Use `right`. Apply `hL2` to reduce the goal to its premises.

Introduce `hH0`. Apply `hx` to reduce the goal to its premises. Simplify using `[hGx, hH0]`. Use `left`. Conclude with `hL1 x hGx`.

Consider the case `smul c G _ hG`. Take `⟨L, hL, hLx⟩` from `hG`. Conclude with `⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`.

Take `⟨φ, g, hg, rfl⟩` from `hG`. Conclude with `integrable_tensor φ hg k`. Consider the case `zero => simp`. Consider the case `add G H hGm hHm hG hH`. Use `(hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Conclude with `(integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m) (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)`. Establish `hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k` using `by positivity`. Simplify using `only [Pi.add_apply]`. Rewrite using `[Real.norm_of_nonneg (by positivity), ← add_mul]`. Conclude with `mul_le_mul_of_nonneg_right (norm_add_le _ _) hw`.

Consider the case `smul c G _ hG`. Use `(hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, norm_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem compactSupport_and_integrable_moments :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (F : (Fin m → Ad E) → ℂ),
    F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin m) →
    (∃ L : Set (Fin m → Af E), IsCompact L ∧ ∀ x, F x ≠ 0 → (fun i => pFin E (x i)) ∈ L) ∧
    ∀ k : ℕ, Integrable (fun x => ‖F x‖ * (1 + ‖fun i => pInf E (x i)‖) ^ k)
      (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ _ m F hF
  refine ⟨?_, fun k => ?_⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      refine ⟨tsupport g, hg.2, fun x hx => ?_⟩
      have e : (fun i => pFin E (x i)) = finPartPi x := rfl
      rw [e]
      apply subset_tsupport
      intro h0
      apply hx
      simp only [schwartzBruhatTensorPi, h0, mul_zero]
    | zero => exact ⟨∅, isCompact_empty, fun x hx => absurd rfl hx⟩
    | add G H _ _ hG hH =>
      obtain ⟨L1, h1, hL1⟩ := hG
      obtain ⟨L2, h2, hL2⟩ := hH
      refine ⟨L1 ∪ L2, h1.union h2, fun x hx => ?_⟩
      by_cases hGx : G x = 0
      · right
        apply hL2
        intro hH0
        apply hx
        simp [hGx, hH0]
      · left
        exact hL1 x hGx
    | smul c G _ hG =>
      obtain ⟨L, hL, hLx⟩ := hG
      exact ⟨L, hL, fun x hx => hLx x fun h0 => hx (by simp [h0])⟩
  · induction hF using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      exact integrable_tensor φ hg k
    | zero => simp
    | add G H hGm hHm hG hH =>
      refine (hG.add hH).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (integrable_of_mem_schwartzBruhatPi (K := E) (ι := Fin m)
          (Submodule.add_mem _ hGm hHm)).aestronglyMeasurable.norm.mul (aestronglyMeasurable_weight k)
      · have hw : 0 ≤ (1 + ‖fun i => pInf E (x i)‖) ^ k := by positivity
        simp only [Pi.add_apply]
        rw [Real.norm_of_nonneg (by positivity), ← add_mul]
        exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hw
    | smul c G _ hG =>
      refine (hG.const_mul ‖c‖).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      ring

end GlobalTheory.SchwartzBruhatMoments
