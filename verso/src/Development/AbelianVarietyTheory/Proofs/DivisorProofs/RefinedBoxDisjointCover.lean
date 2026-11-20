import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EboxIsClopen
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Simplify using `only [ebox, Set.mem_setOf_eq, Matrix.add_apply, Matrix.sub_apply, sub_sub]`.
-/
theorem mem_ebox_add_iff {A D : Type} (ϖ : kˣ) (C x Y : Matrix A D k) (r : A → D → ℕ) :
    Y ∈ ebox ϖ (C + x) r ↔ Y - C ∈ ebox ϖ x r := by
  simp only [ebox, Set.mem_setOf_eq, Matrix.add_apply, Matrix.sub_apply, sub_sub]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Simplify using `only [ebox, Set.mem_setOf_eq, Matrix.sub_apply, Matrix.zero_apply, sub_zero]`.
-/
theorem mem_ebox_iff_sub {A D : Type} (ϖ : kˣ) (C Y : Matrix A D k) (r : A → D → ℕ) :
    Y ∈ ebox ϖ C r ↔ Y - C ∈ ebox ϖ 0 r := by
  simp only [ebox, Set.mem_setOf_eq, Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ ϖ hϖ r r' hrr'`. Establish `h1 : valuation k (ϖ : k) ≤ 1` using `hϖ ▸ uniformizer_lt_one.le`. Establish `hsub : ∀ X : Matrix A D k, ebox ϖ X r' ⊆ ebox ϖ X r`. Introduce `X Y hY i j`. Use `(hY i j).trans ?_` and prove the remaining obligations.

Simplify using `only [Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_le_pow_right_of_le_one' h1 (hrr' i j)`. Establish `hself : ∀ X : Matrix A D k, X ∈ ebox ϖ X r'` using `fun X i j => by simp`. Take `⟨S0, hS0⟩` from `(isCompact_ebox ϖ (0 : Matrix A D k) r).elim_finite_subcover (fun x : ebox ϖ (0 : Matrix A D k) r => ebox ϖ x.1 r') (fun x => (isClopen_ebox k A D ϖ _ r').isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hself y⟩)`. Use `haveI : Nonempty (Matrix A D k) := ⟨0⟩`.

Set `f : Matrix A D k → Matrix A D k` to `fun x => Classical.epsilon (fun y => ebox ϖ y r' = ebox ϖ x r')`. Establish `hf : ∀ x, ebox ϖ (f x) r' = ebox ϖ x r'` using `fun x => Classical.epsilon_spec (p := fun y => ebox ϖ y r' = ebox ϖ x r') ⟨x, rfl⟩`. Establish `hf' : ∀ x y, ebox ϖ x r' = ebox ϖ y r' → f x = f y`. Introduce `x y h`. Use `show Classical.epsilon _ = Classical.epsilon _`.

Rewrite using `[h]`. Use `⟨S0.image (fun x => f x.1), fun C => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use extensionality with `Y`. Prove the components needed by the constructor for the conclusion. Introduce `hY`.

Establish `hY0` using `hS0 ((mem_ebox_iff_sub ϖ C Y r).1 hY)`. Take `⟨x, hx, hYx⟩` from `Set.mem_iUnion₂.1 hY0`. Use `Set.mem_iUnion₂.2 ⟨f x.1, Finset.mem_image_of_mem _ hx, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ebox_add_iff, hf]`. Conclude with `hYx`.

Introduce `hY`. Take `⟨z, hz, hYz⟩` from `Set.mem_iUnion₂.1 hY`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 hz`. Rewrite `hYz` using `[mem_ebox_add_iff, hf]`. Rewrite using `[mem_ebox_iff_sub, ← ebox_eq_of_mem x.2]`.

Conclude with `hsub _ hYz`. Introduce `a ha b hb hab`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 ha)`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hb)`. Rewrite using `[Function.onFun, Set.disjoint_left]`.

Introduce `Y hYa hYb`. Apply `hab` to reduce the goal to its premises. Rewrite `hYa`, `hYb` using `[mem_ebox_add_iff]`. Apply `hf'` to reduce the goal to its premises. Rewrite using `[← hf x.1, ← hf y.1, ← ebox_eq_of_mem hYa, ← ebox_eq_of_mem hYb]`.
-/
theorem ebox_eq_biUnion_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [Fintype D] (ϖ : kˣ), IsUnif ϖ → ∀ (r r' : A → D → ℕ), (∀ i j, r i j ≤ r' i j) →
    ∃ S : Finset (Matrix A D k), ∀ C : Matrix A D k, ebox ϖ C r = (⋃ x ∈ S, ebox ϖ (C + x) r') ∧
      (↑S : Set (Matrix A D k)).PairwiseDisjoint (fun x => ebox ϖ (C + x) r') := by
  intro k _ _ _ _ A D _ _ ϖ hϖ r r' hrr'
  classical
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hsub : ∀ X : Matrix A D k, ebox ϖ X r' ⊆ ebox ϖ X r := by
    intro X Y hY i j
    refine (hY i j).trans ?_
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right_of_le_one' h1 (hrr' i j)
  have hself : ∀ X : Matrix A D k, X ∈ ebox ϖ X r' := fun X i j => by simp
  obtain ⟨S0, hS0⟩ := (isCompact_ebox ϖ (0 : Matrix A D k) r).elim_finite_subcover
    (fun x : ebox ϖ (0 : Matrix A D k) r => ebox ϖ x.1 r') (fun x => (isClopen_ebox k A D ϖ _ r').isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hself y⟩)
  haveI : Nonempty (Matrix A D k) := ⟨0⟩
  let f : Matrix A D k → Matrix A D k := fun x => Classical.epsilon (fun y => ebox ϖ y r' = ebox ϖ x r')
  have hf : ∀ x, ebox ϖ (f x) r' = ebox ϖ x r' := fun x => Classical.epsilon_spec (p := fun y => ebox ϖ y r' = ebox ϖ x r') ⟨x, rfl⟩
  have hf' : ∀ x y, ebox ϖ x r' = ebox ϖ y r' → f x = f y := by
    intro x y h
    show Classical.epsilon _ = Classical.epsilon _
    rw [h]
  refine ⟨S0.image (fun x => f x.1), fun C => ⟨?_, ?_⟩⟩
  · ext Y
    constructor
    · intro hY
      have hY0 := hS0 ((mem_ebox_iff_sub ϖ C Y r).1 hY)
      obtain ⟨x, hx, hYx⟩ := Set.mem_iUnion₂.1 hY0
      refine Set.mem_iUnion₂.2 ⟨f x.1, Finset.mem_image_of_mem _ hx, ?_⟩
      rw [mem_ebox_add_iff, hf]
      exact hYx
    · intro hY
      obtain ⟨z, hz, hYz⟩ := Set.mem_iUnion₂.1 hY
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hz
      rw [mem_ebox_add_iff, hf] at hYz
      rw [mem_ebox_iff_sub, ← ebox_eq_of_mem x.2]
      exact hsub _ hYz
  · intro a ha b hb hab
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    rw [Function.onFun, Set.disjoint_left]
    intro Y hYa hYb
    apply hab
    rw [mem_ebox_add_iff] at hYa hYb
    apply hf'
    rw [← hf x.1, ← hf y.1, ← ebox_eq_of_mem hYa, ← ebox_eq_of_mem hYb]

end GlobalTheory.NormalCore
