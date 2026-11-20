import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelMassDegreeTypeLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermPartitionPartsMulCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMulStatement

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

/- English proof (translation)
Introduce `g _ N A`. Use `set S : Finset (Multiset ℕ) := ((sqSet g N).filter fun f => A (degType g f)).image (degType g) with hS`. Establish `hmem : ∀ μ ∈ S, A μ ∧ (∀ d ∈ μ, 0 < d) ∧ μ.sum = N`. Introduce `μ hμ`. Take `⟨f, hf, rfl⟩` from `Finset.mem_image.1 hμ`.

Rewrite `hf` using `[Finset.mem_filter]`. Take `⟨-, -, hsum, hpos⟩` from `(GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf.1`. Conclude with `⟨hf.2, hpos, hsum⟩`. Establish `hfac : (0 : ℝ) < N.factorial` using `by exact_mod_cast N.factorial_pos`. Establish `hμ : ∀ μ ∈ S, (mass g N fun f => degType g f = μ) ≤ ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card : ℝ) / (N.factorial : ℝ)`.

Introduce `μ hμS`. Take `⟨-, hpos, hsum⟩` from `hmem μ hμS`. Establish `hc` using `congrArg (Nat.cast : ℕ → ℝ) (GlobalTheory.T.card_perm_partition_parts_mul_centralizer N μ hpos hsum)`. Move the coercions through the operations in `at hc`. Establish `hprod : (0 : ℝ) < ∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * ((μ.count d).factorial : ℝ))`.

Use `Finset.prod_pos fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hpos d (Multiset.mem_toFinset.1 hd)`. Establish `hf0 : (0 : ℝ) < ((μ.count d).factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Check the signs of the components of the expression. Establish `hP` using `hprod.ne'`.

Establish `hcard : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card : ℝ) ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, zero_mul]`. Conclude with `hfac.ne' hc.symm`. Use `(GlobalTheory.T.squarefreeLabelMass_degreeType_le g N μ).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[← hc]`. Clear the denominators using the available nonvanishing facts. Establish `hsplit : (mass g N fun f => A (degType g f)) = ∑ μ ∈ S, (mass g N fun f => degType g f = μ)`. Unfold `mass`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := (sqSet g N).filter fun f => A (degType g f)) (t := S) (g := degType g) (fun f hf => Finset.mem_image_of_mem _ hf)]`.

Use `Finset.sum_congr rfl fun μ hμS => Finset.sum_congr ?_ fun _ _ => rfl` and prove the remaining obligations. Use extensionality with `f`. Simplify using `only [Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hf, -⟩, h⟩`.

Conclude with `⟨hf, h⟩`. Introduce and unpack `⟨hf, h⟩`. Conclude with `⟨⟨hf, h ▸ (hmem μ hμS).1⟩, h⟩`. Establish `hperm : ∑ μ ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card : ℝ) = ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card : ℝ)`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S) (t := S) (f := fun σ => σ.partition.parts) (fun σ hσ => (Finset.mem_filter.1 hσ).2)]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `σ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨‹_›, rfl⟩`. Introduce and unpack `⟨-, h⟩`. Conclude with `h`.

Establish `hsub : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card ≤ (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card`. Use `Finset.card_le_card fun σ hσ => ?_` and prove the remaining obligations. Rewrite `hσ`, the goal using `[Finset.mem_filter]`. Conclude with `⟨hσ.1, (hmem _ hσ.2).1⟩`. Rewrite using `[hsplit]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mass_degType_le_cycleType : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (A : Multiset ℕ → Prop),
    (mass g N fun f => A (degType g f)) ≤
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card : ℝ) / (N.factorial : ℝ) := by
  intro g _ N A
  set S : Finset (Multiset ℕ) :=
    ((sqSet g N).filter fun f => A (degType g f)).image (degType g) with hS
  have hmem : ∀ μ ∈ S, A μ ∧ (∀ d ∈ μ, 0 < d) ∧ μ.sum = N := by
    intro μ hμ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hμ
    rw [Finset.mem_filter] at hf
    obtain ⟨-, -, hsum, hpos⟩ := (GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf.1
    exact ⟨hf.2, hpos, hsum⟩
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hμ : ∀ μ ∈ S, (mass g N fun f => degType g f = μ) ≤
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card : ℝ) /
        (N.factorial : ℝ) := by
    intro μ hμS
    obtain ⟨-, hpos, hsum⟩ := hmem μ hμS
    have hc := congrArg (Nat.cast : ℕ → ℝ) (GlobalTheory.T.card_perm_partition_parts_mul_centralizer N μ hpos hsum)
    push_cast at hc
    have hprod : (0 : ℝ) < ∏ d ∈ μ.toFinset, ((d : ℝ) ^ μ.count d * ((μ.count d).factorial : ℝ)) := by
      refine Finset.prod_pos fun d hd => ?_
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d (Multiset.mem_toFinset.1 hd)
      have hf0 : (0 : ℝ) < ((μ.count d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      positivity
    have hP := hprod.ne'
    have hcard : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        σ.partition.parts = μ).card : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hc
      exact hfac.ne' hc.symm
    refine (GlobalTheory.T.squarefreeLabelMass_degreeType_le g N μ).trans (le_of_eq ?_)
    rw [← hc]
    field_simp
  have hsplit : (mass g N fun f => A (degType g f)) =
      ∑ μ ∈ S, (mass g N fun f => degType g f = μ) := by
    unfold mass
    rw [← Finset.sum_fiberwise_of_maps_to (s := (sqSet g N).filter fun f => A (degType g f))
      (t := S) (g := degType g) (fun f hf => Finset.mem_image_of_mem _ hf)]
    refine Finset.sum_congr rfl fun μ hμS => Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hf, -⟩, h⟩
      exact ⟨hf, h⟩
    · rintro ⟨hf, h⟩
      exact ⟨⟨hf, h ▸ (hmem μ hμS).1⟩, h⟩
  have hperm : ∑ μ ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        σ.partition.parts = μ).card : ℝ) =
      ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      σ.partition.parts ∈ S) (t := S) (f := fun σ => σ.partition.parts)
      (fun σ hσ => (Finset.mem_filter.1 hσ).2)]
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨‹_›, rfl⟩
    · rintro ⟨-, h⟩
      exact h
  have hsub : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card ≤
      (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => A σ.partition.parts).card := by
    refine Finset.card_le_card fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨hσ.1, (hmem _ hσ.2).1⟩
  rw [hsplit]
  calc ∑ μ ∈ S, (mass g N fun f => degType g f = μ)
      ≤ ∑ μ ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
          σ.partition.parts = μ).card : ℝ) / (N.factorial : ℝ) := Finset.sum_le_sum hμ
    _ = ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts ∈ S).card : ℝ) /
          (N.factorial : ℝ) := by rw [← Finset.sum_div, hperm]
    _ ≤ _ := by
        gcongr

end GlobalTheory.BadShare
