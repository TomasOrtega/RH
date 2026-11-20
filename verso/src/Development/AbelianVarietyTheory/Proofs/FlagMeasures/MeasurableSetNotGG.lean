import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.WUnfold

variable {k r : ℕ}

/- English proof (translation)
Establish `hs' : sᴴ * Hpk k r * s = Hpk k r` using `hs`. Establish `: (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = xᴴ * Hpk k r * x := by rw [hs']`. Use `show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r`. Rewrite using `[this]`.
-/
theorem mul_mem_GG_iff {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * sᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
          simp only [Matrix.mul_assoc]
      _ = xᴴ * Hpk k r * x := by rw [hs']
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

/- English proof (translation)
Introduce and unpack `s ⟨h, hh, m, hm, rfl⟩`. Conclude with `(mul_mem_GG_iff hh.1).2 hm.1`.
-/
theorem Sset_subset (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

/- English proof (translation)
Establish `hc : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `hc' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r}` using `hc`. Conclude with `hc'.measurableSet.compl`.
-/
theorem measurableSet_not_GG : MeasurableSet {x : Mt k r | Matrix.of x ∉ GG k r} := by
  have hc : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hc' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hc
  exact hc'.measurableSet.compl

/- English proof (translation)
Use `set U : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hU`. Establish `hUm : MeasurableSet U` using `measurableSet_not_GG`. Establish `haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z` using `hS.2.2.1`. Establish `h1` using `hq (U.indicator 1) (measurable_const.indicator hUm)`. Rewrite `h1` using `[lintegral_indicator_one hUm, hG.2.2.1]`.

Establish `h2 : ∫⁻ x, U.indicator (fun _ => μS Set.univ) x ∂ν ≤ 0`. Rewrite using `[h1]`. Use `lintegral_mono fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Rewrite using `[Set.indicator_of_mem hx, ← lintegral_one]`.

Use `lintegral_mono_ae (haeS.mono fun s hs => ?_)` and prove the remaining obligations. Establish `: (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈ U` using `fun h => hx ((mul_mem_GG_iff (Sset_subset z hs)).1 h)`. Rewrite using `[Set.indicator_of_mem this]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx]`.

Conclude with `zero_le`. Rewrite `h2` using `[lintegral_indicator_const hUm, nonpos_iff_eq_zero, mul_eq_zero]`. Break down `h2 with h | h` into its components or cases. Conclude with `absurd (Measure.measure_univ_eq_zero.1 h) hS.2.1`. Conclude with `h`.
-/
theorem ae_mem_GG {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  set U : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hU
  have hUm : MeasurableSet U := measurableSet_not_GG
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := hS.2.2.1
  have h1 := hq (U.indicator 1) (measurable_const.indicator hUm)
  rw [lintegral_indicator_one hUm, hG.2.2.1] at h1
  have h2 : ∫⁻ x, U.indicator (fun _ => μS Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine lintegral_mono_ae (haeS.mono fun s hs => ?_)
      have : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈ U := fun h =>
        hx ((mul_mem_GG_iff (Sset_subset z hs)).1 h)
      rw [Set.indicator_of_mem this]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [lintegral_indicator_const hUm, nonpos_iff_eq_zero, mul_eq_zero] at h2
  rcases h2 with h | h
  · exact absurd (Measure.measure_univ_eq_zero.1 h) hS.2.1
  · exact h

end GlobalTheory.SgInf.WUnfold
