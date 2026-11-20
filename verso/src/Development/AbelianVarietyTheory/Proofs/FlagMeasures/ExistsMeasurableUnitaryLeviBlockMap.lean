import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ isClosedEmbeddingMatrix)

noncomputable section

namespace GlobalTheory.LeviIso

/- English proof (translation)
Establish `hdet : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det` using `(continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_det`. Establish `hadj : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate` using `(continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_adjugate`. Use `measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => ?_` and prove the remaining obligations. Establish `key : (fun x : Fin m → Fin m → ℂ => (Matrix.of x)⁻¹ r s) = fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate r s`. Use function extensionality and compare the values at `x`.

Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[key]`. Conclude with `(hdet.measurable.inv).mul (((continuous_apply s).comp ((continuous_apply r).comp hadj)).measurable)`.
-/
theorem measurable_matInv (m : ℕ) :
    Measurable fun x : Fin m → Fin m → ℂ => (fun r s => (Matrix.of x)⁻¹ r s : Fin m → Fin m → ℂ) := by

  have hdet : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_det
  have hadj : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_adjugate
  refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => ?_
  have key : (fun x : Fin m → Fin m → ℂ => (Matrix.of x)⁻¹ r s) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate r s := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  exact (hdet.measurable.inv).mul
    (((continuous_apply s).comp ((continuous_apply r).comp hadj)).measurable)

/- English proof (translation)
Establish `h : Topology.IsClosedEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)` using `(isClosedEmbeddingMatrix n ε).1`. Conclude with `h.measurableEmbedding`.
-/
theorem measurableEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) := by

  have h : Topology.IsClosedEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) :=
    (isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

/- English proof (translation)
Set `Φ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) → Fin n → Fin n → ℂ` to `fun w r s => (∑ i, B i * Matrix.of (w.1 i) * (B i)ᴴ + ∑ i, Jm ε * B i * (Matrix.of (w.2.1 i))ᴴ * (B i)ᴴ * Jm ε + B₀ * Matrix.of w.2.2 * B₀ᴴ) r s`. Establish `hΦ : Continuous Φ`. Use `continuous_pi fun r => continuous_pi fun s => ?_` and prove the remaining obligations. Use `Continuous.matrix_elem ?_ r s` and prove the remaining obligations. Use `Continuous.add (Continuous.add ?_ ?_) ?_` and prove the remaining obligations.

Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(continuous_const.matrix_mul ((continuous_apply i).comp continuous_fst : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.1 i)))).matrix_mul continuous_const`. Use `continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Conclude with `((continuous_const.matrix_mul ((continuous_apply i).comp (continuous_fst.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.2.1 i))).matrix_conjTranspose).matrix_mul continuous_con …`. Conclude with `(continuous_const.matrix_mul ((continuous_snd.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of w.2.2))).matrix_mul continuous_const`.

Establish `hinv : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (fun i r s => (Matrix.of (z.1 i))⁻¹ r s : ∀ i, Fin (j i) → Fin (j i) → ℂ)` using `measurable_pi_lambda _ fun i => (measurable_matInv (j i)).comp ((measurable_pi_apply i).comp measurable_fst)`. Establish `hg : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (fun r s => uMat z.2 r s : Fin n₀ → Fin n₀ → ℂ)` using `(measurableEmbedding_uMat ε₀).measurable.comp measurable_snd`. Establish `hcomp` using `hΦ.measurable.comp (measurable_fst.prodMk (hinv.prodMk hg))`. Use `hcomp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z r s`.

Simplify using `only [Function.comp_apply, Φ, lev]`. Both sides reduce to the same expression.
-/
theorem measurable_lev {n n₀ a : ℕ} {j : Fin a → ℕ} (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) :
    Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ) := by

  let Φ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) →
      Fin n → Fin n → ℂ := fun w r s =>
    (∑ i, B i * Matrix.of (w.1 i) * (B i)ᴴ + ∑ i, Jm ε * B i * (Matrix.of (w.2.1 i))ᴴ * (B i)ᴴ * Jm ε +
      B₀ * Matrix.of w.2.2 * B₀ᴴ) r s
  have hΦ : Continuous Φ := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    refine Continuous.matrix_elem ?_ r s
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.matrix_mul
        ((continuous_apply i).comp continuous_fst : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.1 i)))).matrix_mul
        continuous_const
    · refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_const.matrix_mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd) : Continuous fun w :
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) =>
            (Matrix.of (w.2.1 i))).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        continuous_const
    · exact (continuous_const.matrix_mul
        ((continuous_snd.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of w.2.2))).matrix_mul
        continuous_const
  have hinv : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun i r s => (Matrix.of (z.1 i))⁻¹ r s : ∀ i, Fin (j i) → Fin (j i) → ℂ) :=
    measurable_pi_lambda _ fun i =>
      (measurable_matInv (j i)).comp ((measurable_pi_apply i).comp measurable_fst)
  have hg : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => uMat z.2 r s : Fin n₀ → Fin n₀ → ℂ) :=
    (measurableEmbedding_uMat ε₀).measurable.comp measurable_snd
  have hcomp := hΦ.measurable.comp (measurable_fst.prodMk (hinv.prodMk hg))
  convert hcomp using 1
  funext z r s
  simp only [Function.comp_apply, Φ, lev]
  rfl

/- English proof (translation)
Set `S : Set ((∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀)` to `{z | ∀ i, (Matrix.of (z.1 i)).det ≠ 0}`. Establish `hex : ∀ z ∈ S, ∃ g : UJ ε, uMat g = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)`. Introduce `z hz`. Establish `hU : inUJ ε (lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2))` using `h.inUJ_lev _ _ hz z.2.2`. Establish `hr : lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) ∈ Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))`.

Rewrite using `[(isClosedEmbeddingMatrix n ε).2]`. Conclude with `hU`. Take `⟨g, hg⟩` from `hr`. Conclude with `⟨g, hg⟩`. Set `θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε` to `fun z => if hz : z ∈ S then (hex z hz).choose else 1`.

Establish `hθ : ∀ z ∈ S, uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)`. Introduce `z hz`. Simplify using `only [θ, dif_pos hz]`. Conclude with `(hex z hz).choose_spec`. Use `⟨θ, ?_, fun z hz => hθ z hz⟩` and prove the remaining obligations.

Establish `hdet : ∀ i, Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det` using `fun i =>`. Establish `hc : Continuous fun x : Fin (j i) → Fin (j i) → ℂ => (Matrix.of x).det` using `(continuous_id (X := Matrix (Fin (j i)) (Fin (j i)) ℂ)).matrix_det`. Use the proof step `hc.measurable.comp ((measurable_pi_apply i).comp measurable_fst)`. Establish `hS : MeasurableSet S`. Establish `: S = ⋂ i, (fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det) ⁻¹' {0}ᶜ`.

Use extensionality with `z`. Simplify using `[S]`. Rewrite using `[this]`. Conclude with `MeasurableSet.iInter fun i => (hdet i) (measurableSet_singleton 0).compl`. Rewrite using `[← (measurableEmbedding_uMat ε).measurable_comp_iff]`.

Establish `heq : ((fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)) ∘ θ) = fun z => if z ∈ S then (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ) else (fun r s => uMat (1 : UJ ε) r s)`. Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ S`. Simplify using `only [Function.comp_apply, if_pos hz, hθ z hz]`. Simplify using `only [Function.comp_apply, if_neg hz, θ, dif_neg hz]`.

Rewrite using `[heq]`. Conclude with `Measurable.ite hS (measurable_lev ε ε₀ B B₀) measurable_const`.
-/
theorem exists_measurable_levMap (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (h : IsFrame ε ε₀ B B₀) :
    ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε, Measurable θ ∧
      ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
        uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  classical

  let S : Set ((∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀) := {z | ∀ i, (Matrix.of (z.1 i)).det ≠ 0}
  have hex : ∀ z ∈ S, ∃ g : UJ ε, uMat g = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    have hU : inUJ ε (lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) := h.inUJ_lev _ _ hz z.2.2
    have hr : lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact hU
    obtain ⟨g, hg⟩ := hr
    exact ⟨g, hg⟩
  let θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε := fun z =>
    if hz : z ∈ S then (hex z hz).choose else 1
  have hθ : ∀ z ∈ S, uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    simp only [θ, dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨θ, ?_, fun z hz => hθ z hz⟩
  have hdet : ∀ i, Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det :=
    fun i =>
      have hc : Continuous fun x : Fin (j i) → Fin (j i) → ℂ => (Matrix.of x).det :=
        (continuous_id (X := Matrix (Fin (j i)) (Fin (j i)) ℂ)).matrix_det
      hc.measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det) ⁻¹' {0}ᶜ := by
      ext z
      simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => (hdet i) (measurableSet_singleton 0).compl
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have heq : ((fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)) ∘ θ) = fun z =>
      if z ∈ S then (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ)
      else (fun r s => uMat (1 : UJ ε) r s) := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Function.comp_apply, if_pos hz, hθ z hz]
    · simp only [Function.comp_apply, if_neg hz, θ, dif_neg hz]
  rw [heq]
  exact Measurable.ite hS (measurable_lev ε ε₀ B B₀) measurable_const

end GlobalTheory.LeviIso
