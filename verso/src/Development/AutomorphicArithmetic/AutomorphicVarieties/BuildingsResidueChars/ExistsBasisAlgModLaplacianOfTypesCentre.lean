import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotCompactCasimirOfTypes
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Use `UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B) (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))` and prove the remaining obligations. Introduce `x hx y hy`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm`. Introduce `T hT`.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT`. Apply the tactic sequence `rcases hT with rfl | rfl <;> assumption`.
-/
private theorem algMod_add {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (A B : Module.End ℂ M)
    (hAB : A * B = B * A) (hA : AlgMod S ⊥ A) (hB : AlgMod S ⊥ B) : AlgMod S ⊥ (A + B) := by
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B)
    (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl <;> assumption

/- English proof (translation)
Introduce `K _ _ n S hT hC`. Take `⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩` from `exists_archCartanData K n`. Use `⟨d, b, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num`. Establish `hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU` using `casimir_mem_center hε2 horth hsymm hinv`.

Rewrite using `[laplacianU_eq_casimir_add b ε, map_add]`. Use `algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_` and prove the remaining obligations. Use `UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_` and prove the remaining obligations. Break down `hε i with e | e` into its components or cases. Conclude with `Or.inl (by rw [e, sub_self])`.

Conclude with `Or.inr (hK i e)`.
-/
theorem UpperTheory.exists_basis_algMod_laplacian_of_types_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → Centre S → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra), AlgMod S ⊥ (uAction (laplacianU K n b)) := by
  intro K _ _ n S hT hC
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  refine ⟨d, b, ?_⟩
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU := casimir_mem_center hε2 horth hsymm hinv
  rw [laplacianU_eq_casimir_add b ε, map_add]
  refine algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_
  refine UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_
  rcases hε i with e | e
  · exact Or.inl (by rw [e, sub_self])
  · exact Or.inr (hK i e)
