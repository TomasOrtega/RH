import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.LeastDegree

/- English proof (translation)
Take `⟨ht, -, -, -, -, -, -, -, -, -, habs⟩` from `h`. Establish `key : ∀ e ∈ al ++ be ++ ga ++ de, e ≠ 0`. Introduce `e he h0`. Establish `hle` using `habs e he`. Rewrite `hle` using `[h0, abs_zero]`.

Establish `ht' : (1 : ℚ) ≤ t` using `by exact_mod_cast ht`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `a with ⟨i, hi⟩ | ⟨j, hj⟩` into its components or cases. Establish `hi' : i < (al ++ be).length` using `by simpa using hi`. Establish `hm : (al ++ be)[i] ∈ al ++ be` using `List.getElem_mem hi'`.

Simplify using `only [lamA, ofBlocks, List.getD_eq_getElem _ _ hi']`. Apply `key` to reduce the goal to its premises. Simplify using `only [List.mem_append] at hm ⊢`. The claim follows by propositional logic. Establish `hj' : j < (ga ++ de).length` using `by simpa using hj`.

Establish `hm : (ga ++ de)[j] ∈ ga ++ de` using `List.getElem_mem hj'`. Simplify using `only [lamA, ofBlocks, List.getD_eq_getElem _ _ hj']`. Apply `key` to reduce the goal to its premises. Simplify using `only [List.mem_append] at hm ⊢`. The claim follows by propositional logic.
-/
theorem lamA_ne_zero {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de)
    (a : Ix (al.length + be.length) (ga.length + de.length)) : lamA al be ga de a ≠ 0 := by
  obtain ⟨ht, -, -, -, -, -, -, -, -, -, habs⟩ := h
  have key : ∀ e ∈ al ++ be ++ ga ++ de, e ≠ 0 := by
    intro e he h0
    have hle := habs e he
    rw [h0, abs_zero] at hle
    have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hi' : i < (al ++ be).length := by simpa using hi
    have hm : (al ++ be)[i] ∈ al ++ be := List.getElem_mem hi'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hi']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto
  · have hj' : j < (ga ++ de).length := by simpa using hj
    have hm : (ga ++ de)[j] ∈ ga ++ de := List.getElem_mem hj'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hj']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto

/- English proof (translation)
Introduce `μ v hv`. Conclude with `(hX p q lam h).2.2 μ v hv`.
-/
theorem coneTypes_ds (X : ProvA) (hX : DiscreteSeriesBlattner X) {p q : ℕ} {lam : Ix p q → ℚ}
    (h : IsParam lam) : ConeTypes (X.ds p q lam).HK lam := by
  intro μ v hv
  exact (hX p q lam h).2.2 μ v hv

/- English proof (translation)
Introduce `X hX t al be ga de hA`. Take `⟨-, hP, hP', hs, hs'⟩` from `GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_` and prove the remaining obligations. Introduce `a`.

Use `⟨(hs a).1, fun hle => (hs a).2 ?_⟩` and prove the remaining obligations. Conclude with `lt_of_le_of_ne hle (lamA_ne_zero hA a)`. Conclude with `GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hP') hs'`.
-/
theorem lowest_least_degree : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length + t) (ga.length + be.length)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamA' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, hP', hs, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hP') hs'

/- English proof (translation)
Introduce `X hX t al be ga de hA`. Take `⟨-, hP, -, -, -⟩` from `GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA`. Take `⟨-, hM, hs, hs'⟩` from `GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_` and prove the remaining obligations.

Introduce `a`. Use `⟨(hs a).1, fun hle => (hs a).2 ?_⟩` and prove the remaining obligations. Conclude with `lt_of_le_of_ne hle (lamA_ne_zero hA a)`. Conclude with `GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hM) hs'`.
-/
theorem lowest_least_degree_mirror : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length) (ga.length + be.length + t)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamM' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, -, -, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨-, hM, hs, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hM) hs'

end GlobalTheory.LeastDegree
