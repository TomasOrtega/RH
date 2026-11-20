import Mathlib
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.HermitianCommuting

/- English proof (translation)
Set `S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))` to `{a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}`. Establish `hS : S.Nonempty`. Use `⟨⊥, bot_le, ?_, ?_⟩` and prove the remaining obligations. Introduce `A hA`. Rewrite `hA` using `[Submodule.mem_bot]`.

Simplify using `[hA]`. Introduce `A hA B hB`. Rewrite `hA`, `hB` using `[Submodule.mem_bot]`. Simplify using `[hA, hB]`. Take `⟨a, ha, hmax⟩` from `(wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS`.

Use `⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩` and prove the remaining obligations. Introduce `Y hY hYh hYc`. Establish `hmem : a ⊔ Submodule.span ℝ {Y} ∈ S`. Use `⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩` and prove the remaining obligations. Introduce `A hA`.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hA`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Rewrite using `[conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]`. Simplify using the standard rewrite rules. Introduce `A hA B hB`.

Take `⟨x, hx, y, hy, rfl⟩` from `Submodule.mem_sup.1 hA`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Take `⟨x', hx', y', hy', rfl⟩` from `Submodule.mem_sup.1 hB`. Take `⟨d, rfl⟩` from `Submodule.mem_span_singleton.1 hy'`. Establish `h1` using `ha.2.2 x hx x' hx'`.

Establish `h2` using `hYc x hx`. Establish `h3` using `hYc x' hx'`. Simplify using `only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]`. Rewrite using `[mul_comm d c]`. Normalize the expressions using the abelian group laws.

Establish `hne : a ⊔ Submodule.span ℝ {Y} = a`. Assume the negation of the conclusion as `h`. Conclude with `hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))`. Establish `hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y}` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)`. Rewrite `hYmem` using `[hne]`. Then use the resulting hypothesis.
-/
theorem exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  let S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    {a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}
  have hS : S.Nonempty := by
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · intro A hA
      rw [Submodule.mem_bot] at hA
      simp [hA]
    · intro A hA B hB
      rw [Submodule.mem_bot] at hA hB
      simp [hA, hB]
  obtain ⟨a, ha, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩
  intro Y hY hYh hYc
  have hmem : a ⊔ Submodule.span ℝ {Y} ∈ S := by
    refine ⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]
      simp
    · intro A hA B hB
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hB
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have h1 := ha.2.2 x hx x' hx'
      have h2 := hYc x hx
      have h3 := hYc x' hx'
      simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]
      rw [mul_comm d c]
      abel
  have hne : a ⊔ Submodule.span ℝ {Y} = a := by
    by_contra h
    exact hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))
  have hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)
  rwa [hne] at hYmem

end GlobalTheory.CompanionTheory.HermitianCommuting
