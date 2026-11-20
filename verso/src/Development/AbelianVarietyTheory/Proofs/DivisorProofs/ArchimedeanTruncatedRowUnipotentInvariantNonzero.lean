import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

/- English proof (translation)
Introduce `E _ _ n ρ g hg`. Establish `hw : ∀ w, compGL w g ∈ levSet n (ρ + 1)` using `hg`. Establish `hc : ∀ w (x : GL (Fin n) (Cinf E)) j, rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j = rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w`. Introduce `w x j`. Unfold `rowCut rowCutInf`.

Apply the tactic sequence `split_ifs <;> rfl`. Prove the components needed by the constructor for the conclusion. Introduce `u hu`. Take `⟨hu0, hu1⟩` from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu`. Establish `hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n)`.

Introduce `w`. Use `(GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[compGL_apply, hu0 i j h]`. Both sides reduce to the same expression. Rewrite using `[compGL_apply, hu1 i]`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `j w`. Rewrite using `[← hc, ← hc, map_mul]`. Conclude with `congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j`. Introduce `w`.

Take `⟨j, hj, hne⟩` from `(truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2`. Conclude with `⟨j, hj, by rwa [← hc]⟩`.
-/
theorem rowCutInf_unipB_mul_levSetInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n),
    ∀ g ∈ levSetInf E n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) =
      rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧
    ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  intro E _ _ n ρ g hg
  have hw : ∀ w, compGL w g ∈ levSet n (ρ + 1) := hg
  have hc : ∀ w (x : GL (Fin n) (Cinf E)) j,
      rowCut ρ ((compGL w x : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) j =
        rowCutInf ρ (x : Matrix (Fin n) (Fin n) (Cinf E)) j w := by
    intro w x j
    unfold rowCut rowCutInf
    split_ifs <;> rfl
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    have hmem : ∀ w, compGL w u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n) := by
      intro w
      refine (GlobalTheory.SmGL.mem_unipB ℂ).2 ⟨fun i j h => ?_, fun i => ?_⟩
      · rw [compGL_apply, hu0 i j h]; rfl
      · rw [compGL_apply, hu1 i]; rfl
    funext j w
    rw [← hc, ← hc, map_mul]
    exact congrFun ((truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).1 _ (hmem w)) j
  · intro w
    obtain ⟨j, hj, hne⟩ := (truncatedRow_unipotent_mul_and_ne_zero n ρ _ (hw w)).2
    exact ⟨j, hj, by rwa [← hc]⟩

end GlobalTheory.JSW.MirCinf
