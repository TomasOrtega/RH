import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

def gen {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) :
    (D × List (Fin n)) × (path ⟨D, E, hE⟩ χ ss).V → (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  fun p => famP σ D E hE χ ss p.1 p.2

def SS {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  Submodule.span ℂ (Set.range (gen σ D E hE χ ss))

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨(i, u), rfl⟩`.
-/
theorem gen_mem {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hE : Formalism.REAL.GlRel E) (χ : Fin n → ℂ) (ss : List (Fin n)) (i : D × List (Fin n))
    (u : (path ⟨D, E, hE⟩ χ ss).V) : famP σ D E hE χ ss i u ∈ SS σ D E hE χ ss :=
  Submodule.subset_span ⟨(i, u), rfl⟩

/- English proof (translation)
Break down `I.eq_empty_or_nonempty with hI | hI` into its components or cases. Conclude with `⟨∅, by simp, fun x => by simp [hI]⟩`. Use `set N : ℝ := (I.card : ℝ) with hN`. Establish `hN1 : 1 ≤ N` using `by rw [hN]; exact_mod_cast Finset.card_pos.mpr hI`. Use `⟨I.image (fun i => (N : ℂ) • h i), ?_, fun x => ?_⟩` and prove the remaining obligations.

Introduce `f hf`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.mp hf`. Conclude with `S.smul_mem _ (hS i hi)`. Establish `key : ∀ i ∈ I, N * ‖h i x‖ ^ e ≤ ∑ f ∈ I.image (fun i => (N : ℂ) • h i), ‖f x‖ ^ e`. Introduce `i hi`.

Establish `h1 : N * ‖h i x‖ ^ e ≤ ‖((N : ℂ) • h i) x‖ ^ e`. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1.trans (Finset.single_le_sum (f := fun f : M → ℂ => ‖f x‖ ^ e) (fun _ _ => by positivity) (Finset.mem_image_of_mem _ hi))`.

Establish `hsum` using `Finset.sum_le_sum key`. Rewrite `hsum` using `[← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]`. Establish `hpos : (0 : ℝ) < N` using `by linarith`. Rewrite `hsum` using `[← hN]`. Conclude with `le_of_mul_le_mul_left hsum hpos`.
-/
theorem absorb {M α : Type*} (S : Submodule ℂ (M → ℂ)) (I : Finset α) (h : α → (M → ℂ))
    (hS : ∀ i ∈ I, h i ∈ S) (e : ℕ) (he : 1 ≤ e) :
    ∃ T : Finset (M → ℂ), (∀ f ∈ T, f ∈ S) ∧ ∀ x, ∑ i ∈ I, ‖h i x‖ ^ e ≤ ∑ f ∈ T, ‖f x‖ ^ e := by
  classical
  rcases I.eq_empty_or_nonempty with hI | hI
  · exact ⟨∅, by simp, fun x => by simp [hI]⟩
  set N : ℝ := (I.card : ℝ) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hI
  refine ⟨I.image (fun i => (N : ℂ) • h i), ?_, fun x => ?_⟩
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
    exact S.smul_mem _ (hS i hi)
  have key : ∀ i ∈ I, N * ‖h i x‖ ^ e ≤ ∑ f ∈ I.image (fun i => (N : ℂ) • h i), ‖f x‖ ^ e := by
    intro i hi
    have h1 : N * ‖h i x‖ ^ e ≤ ‖((N : ℂ) • h i) x‖ ^ e := by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ e := pow_le_pow_right₀ hN1 he
    exact h1.trans (Finset.single_le_sum (f := fun f : M → ℂ => ‖f x‖ ^ e) (fun _ _ => by positivity)
      (Finset.mem_image_of_mem _ hi))
  have hsum := Finset.sum_le_sum key
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < N := by linarith
  rw [← hN] at hsum
  exact le_of_mul_le_mul_left hsum hpos

end CompanionTheory.RgExh.Dec.L.SA
