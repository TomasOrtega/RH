import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ConvHecke

/- English proof (translation)
Introduce `H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂`. Establish `hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y))`. Introduce `y l hl x`. Use `show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)`. Establish `e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y)` using `by group`.

Rewrite using `[e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]`. Establish `hlev` using `fun y => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin`. Establish `hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0`. Introduce `y hy`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hy` to reduce the goal to its premises. Rewrite using `[hlev y]`. Establish `hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0`. Introduce `p`.

Distinguish the cases in `h : f₁ p.out = 0`. Simplify using `[h]`. Simplify using `[hcon _ h]`. Simplify using `[hz]`. Use `⟨⟨?_, ?_⟩, hnz⟩` and prove the remaining obligations.

Use `HasCompactSupport.of_support_subset_isCompact (h₁.1.isCompact.mul h₂.1.isCompact) ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨z, hz1, hz2⟩` from `hnz y hy`. Conclude with `Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩`. Introduce `l hl x`.

Prove the components needed by the constructor for the conclusion. Use `show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)`. Rewrite using `[hlev (l * x), hlev x]`. Use `congr 1`. Use `(finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans (finsum_congr fun p => ?_)` and prove the remaining obligations.

Use `set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw`. Establish `hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L)`. Rewrite using `[hw, QuotientGroup.out_eq']`. Use `show ((l * p.out : H) : H ⧸ L) = l • p`. Use `conv_rhs => rw [← QuotientGroup.out_eq' p]`.

Both sides reduce to the same expression. Establish `hm : (l * p.out)⁻¹ * w ∈ L` using `QuotientGroup.eq.1 hcl`. Establish `hinv` using `hu (l * x) hm (l * p.out)`. Establish `hmul : l * p.out * ((l * p.out)⁻¹ * w) = w` using `by group`. Simplify using `only [hmul] at hinv`.

Use `hinv.trans ?_` and prove the remaining obligations. Establish `e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x` using `by group`. Rewrite using `[e, (h₁.2 l hl _).1]`. Use `show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)`. Establish `e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x)`.

Use function extensionality and compare the values at `z`. Rewrite using `[← mul_assoc, (h₂.2 l hl _).2]`. Rewrite using `[e]`.
-/
theorem conv_isHecke : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
    IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧
      ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  intro H _ _ _ _ K L f₁ f₂ hLK hfin h₁ h₂
  have hu : ∀ y, L ≤ rStab (fun z => f₁ z * f₂ (z⁻¹ * y)) := by
    intro y l hl x
    show f₁ (x * l) * f₂ ((x * l)⁻¹ * y) = f₁ x * f₂ (x⁻¹ * y)
    have e : (x * l)⁻¹ * y = l⁻¹ * (x⁻¹ * y) := by group
    rw [e, (h₁.2 l hl x).2, (h₂.2 l⁻¹ (L.inv_mem hl) _).1]
  have hlev := fun y =>
    GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L (fun z => f₁ z * f₂ (z⁻¹ * y)) hLK (hu y) hfin
  have hnz : ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 →
      ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    apply hy
    rw [hlev y]
    have hz : ∀ p : H ⧸ L, f₁ p.out * f₂ ((p.out)⁻¹ * y) = 0 := by
      intro p
      by_cases h : f₁ p.out = 0
      · simp [h]
      · simp [hcon _ h]
    simp [hz]
  refine ⟨⟨?_, ?_⟩, hnz⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (h₁.1.isCompact.mul h₂.1.isCompact) ?_
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := hnz y hy
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ hz1, z⁻¹ * y, subset_tsupport _ hz2, by group⟩
  · intro l hl x
    constructor
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (l * x))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      rw [hlev (l * x), hlev x]
      congr 1
      refine (finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (H ⧸ L))).symm.trans
        (finsum_congr fun p => ?_)
      set w : H := ((MulAction.toPerm l : Equiv.Perm (H ⧸ L)) p).out with hw
      have hcl : ((l * p.out : H) : H ⧸ L) = (w : H ⧸ L) := by
        rw [hw, QuotientGroup.out_eq']
        show ((l * p.out : H) : H ⧸ L) = l • p
        conv_rhs => rw [← QuotientGroup.out_eq' p]
        rfl
      have hm : (l * p.out)⁻¹ * w ∈ L := QuotientGroup.eq.1 hcl
      have hinv := hu (l * x) hm (l * p.out)
      have hmul : l * p.out * ((l * p.out)⁻¹ * w) = w := by group
      simp only [hmul] at hinv
      refine hinv.trans ?_
      have e : (l * p.out)⁻¹ * (l * x) = (p.out)⁻¹ * x := by group
      rw [e, (h₁.2 l hl _).1]
    · show (hint K fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = hint K fun z => f₁ z * f₂ (z⁻¹ * x)
      have e : (fun z => f₁ z * f₂ (z⁻¹ * (x * l))) = fun z => f₁ z * f₂ (z⁻¹ * x) := by
        funext z
        rw [← mul_assoc, (h₂.2 l hl _).2]
      rw [e]

end GlobalTheory.CompanionTheory.ConvHecke

end
