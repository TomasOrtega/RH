import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

/- English proof (translation)
Set `o` to `stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)`. Set `o'` to `stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)`. Establish `hΦ : (S.T t).Phi j (c + 1) (by omega) w = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') w).submatrix (ixSucc _ t j) id)` using `rfl`. Rewrite `hw` using `[hΦ]`. Establish `hI` using `TypeDatum.intM_of_Phi_ne_zero _ _ hw ((ixSucc _ t j).symm (o.symm (Sum.inr ⟨r, by omega⟩))) (o'.symm (Sum.inl y))`.

Establish `hw' : w = fromBlocks w.toBlocks₁₁ w.toBlocks₁₂ w.toBlocks₂₁ w.toBlocks₂₂` using `(fromBlocks_toBlocks w).symm`. Rewrite `hI` using `[hw']`. Simplify using `[LatFrame.coords, typeFrame, embA, GlobalTheory.SplitFlip.diagGL, fromBlocks_multiply] at hI`. Rewrite `hI` using `[Valuation.mem_integer_iff, map_mul, map_inv₀]`. Establish `hv : 0 < valuation k ((S.ϖ : k) ^ (r + 1))`.

Rewrite using `[zero_lt_iff]`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_pow_eq_pow_val]`. Express the relevant statement in the definitionally equal form `valuation k (w.toBlocks₂₁ ⟨r, by omega⟩ y) ≤ _`. Rewrite `hI` using `[inv_mul_le_iff₀ hv, mul_one]`. Then use the resulting hypothesis.
-/
theorem val_row_le_of_Phi_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + 1 + c = s) (r : ℕ)
    (hc : c = 2 * r) (w : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1)) k)
    (hw : (S.T t).Phi j (c + 1) (by omega) w ≠ 0) (y : XIx (Fin κ) t j) :
    valuation k (w (Sum.inr ⟨r, by omega⟩) (Sum.inl y)) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have hΦ : (S.T t).Phi j (c + 1) (by omega) w = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') w).submatrix (ixSucc _ t j) id) := rfl
  rw [hΦ] at hw
  have hI := TypeDatum.intM_of_Phi_ne_zero _ _ hw ((ixSucc _ t j).symm (o.symm (Sum.inr ⟨r, by omega⟩)))
    (o'.symm (Sum.inl y))
  have hw' : w = fromBlocks w.toBlocks₁₁ w.toBlocks₁₂ w.toBlocks₂₁ w.toBlocks₂₂ := (fromBlocks_toBlocks w).symm
  rw [hw'] at hI
  simp [LatFrame.coords, typeFrame, embA, GlobalTheory.SplitFlip.diagGL, fromBlocks_multiply] at hI
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀] at hI
  have hv : 0 < valuation k ((S.ϖ : k) ^ (r + 1)) := by
    rw [zero_lt_iff]; simp
  rw [Units.val_pow_eq_pow_val]
  change valuation k (w.toBlocks₂₁ ⟨r, by omega⟩ y) ≤ _
  rwa [inv_mul_le_iff₀ hv, mul_one] at hI

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν s κ S t _ _ j c H r hc x hx`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, ¬ valuation k (x (Sum.inr ()) y) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx fun i => h i`.

Unfold `flRow opE`. Use `(integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)).trans (integral_zero _ _)` and prove the remaining obligations. Simplify using `only [Pi.zero_apply]`. Use `mul_eq_zero_of_left ?_ _` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h1` using `val_row_le_of_Phi_ne_zero S t j c H r hc _ hne y`. Apply `hy` to reduce the goal to its premises. Use `h1 using 2` and compare the differences between its conclusion and the goal. Simplify using `[affPt, basePt, rowAt, Free]`.
-/
theorem flRow_eq_zero_of_not_mem_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by
  intro k _ _ _ _ _ _ ν s κ S t _ _ j c H r hc x hx
  obtain ⟨y, hy⟩ : ∃ y, ¬ valuation k (x (Sum.inr ()) y) ≤ valuation k (((S.ϖ ^ (r + 1) : kˣ)) : k) := by
    by_contra h
    push_neg at h
    exact hx fun i => h i
  unfold flRow opE
  refine (integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)).trans (integral_zero _ _)
  simp only [Pi.zero_apply]
  refine mul_eq_zero_of_left ?_ _
  by_contra hne
  have h1 := val_row_le_of_Phi_ne_zero S t j c H r hc _ hne y
  apply hy
  convert h1 using 2
  simp [affPt, basePt, rowAt, Free]
end GlobalTheory.LocFlat
