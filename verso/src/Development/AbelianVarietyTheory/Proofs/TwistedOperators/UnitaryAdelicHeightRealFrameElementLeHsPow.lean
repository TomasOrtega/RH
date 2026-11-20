import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameHeight

def EntryBd {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : ℝ, ∀ g i j, ‖f g i j‖ ≤ c * (1 + Formalism.REAL.hs g)

variable {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Unfold `Formalism.REAL.hs`. Check the signs of the components of the expression.
-/
theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs; positivity

/- English proof (translation)
Use `⟨1, fun g i j => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g`. Unfold `Formalism.REAL.hs`. Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)`.

Use polynomial arithmetic with `[sq_nonneg (‖g i j‖ - 1), hs_nonneg g]`.
-/
theorem entryBd_id : EntryBd (fun g : Matrix (Fin n) (Fin n) ℂ => g) := by
  refine ⟨1, fun g i j => ?_⟩
  have h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g := by
    unfold Formalism.REAL.hs
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i j‖ - 1), hs_nonneg g]

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Conclude with `⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩`.
-/
theorem EntryBd.conjTranspose (h : EntryBd f) : EntryBd fun g => (f g)ᴴ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Use `⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩` and prove the remaining obligations. Establish `h0` using `hs_nonneg g`. Use `show ‖(P * f g) i j‖ ≤ _`. Rewrite using `[Matrix.mul_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left ((hc g k j).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)`. Use `_ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]`.

Use `_ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)`. Use `_ = _ := by ring`.
-/
theorem EntryBd.const_mul (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => P * f g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩
  have h0 := hs_nonneg g
  show ‖(P * f g) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖P i k‖ * (|c| * (1 + Formalism.REAL.hs g)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hc g k j).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)
    _ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖)
          (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)
    _ = _ := by ring

/- English proof (translation)
Simplify using `using (h.conjTranspose.const_mul Pᴴ).conjTranspose`.
-/
theorem EntryBd.mul_const (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => f g * P := by
  simpa using (h.conjTranspose.const_mul Pᴴ).conjTranspose

/- English proof (translation)
Establish `h1 : A.fr τ * (A.fr τ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))`. Establish `hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ)` using `hk`. Establish `h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`. Use `show _ᴴ * _ * _ = _`. Rewrite using `[← A.fr_gram τ]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem frame_mem {D : D7} {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) :
    (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

/- English proof (translation)
Introduce `D θ hθ V A τ`. Take `⟨d, hd⟩` from `GlobalTheory.Grow.height_le_normInf_pow V hθ`. Establish `b1` using `(entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)`. Take `⟨c2, h2⟩` from `(b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)`. Take `⟨c1, h1⟩` from `b1`.

Use `⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hu` using `frame_mem A τ hg`. Establish `s1` using `GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu`. Establish `s2` using `GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1`. Establish `h0` using `hs_nonneg g`.

Use `(hd _ s1.1).trans ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Use `pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d` and prove the remaining obligations. Unfold `normInf`. Simplify using `only [Finset.sum_mul]`.

Use `Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Establish `a1` using `mul_nonneg (abs_nonneg c1) h0`. Establish `a2` using `mul_nonneg (abs_nonneg c2) h0`. Distinguish the cases in `e : ρ = τ`. Substitute `e` using the available equality.

Rewrite using `[s1.2.1, s2.2.1]`. Establish `e1` using `(h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))`. Establish `e2` using `(h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[s1.2.2 ρ e, s2.2.2 ρ e]`.

Establish `: ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1`. Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Use polynomial arithmetic with `[abs_nonneg c1, abs_nonneg c2]`.
-/
theorem height_elt_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  intro D θ hθ V A τ
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow V hθ
  have b1 := (entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)
  obtain ⟨c2, h2⟩ := (b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)
  obtain ⟨c1, h1⟩ := b1
  refine ⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩
  have hu := frame_mem A τ hg
  have s1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  have s2 := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1
  have h0 := hs_nonneg g
  refine (hd _ s1.1).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have a1 := mul_nonneg (abs_nonneg c1) h0
  have a2 := mul_nonneg (abs_nonneg c2) h0
  by_cases e : ρ = τ
  · subst e
    rw [s1.2.1, s2.2.1]
    have e1 := (h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))
    have e2 := (h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))
    nlinarith
  · rw [s1.2.2 ρ e, s2.2.2 ρ e]
    have : ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [abs_nonneg c1, abs_nonneg c2]

end GlobalTheory.FrameHeight
