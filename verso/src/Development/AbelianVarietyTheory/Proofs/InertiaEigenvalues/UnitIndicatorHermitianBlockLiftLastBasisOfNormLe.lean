import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Simplify `h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))` using `[full]`. Simplify `h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr (0 : Fin 1)))` using `[full]`.

Simplify `h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inl j))` using `[full]`. Simplify `h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))` using `[full]`. Introduce and unpack `⟨h1, h2, h3, h4⟩ i j`. Simplify using `only [full, Matrix.reindex_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b`.

Simplify using `using h1 a b`. Simplify using `using h2 a`. Simplify using `using h3 b`. Simplify using `using h4`.
-/
theorem forall_full_entries_iff {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) (P : k → Prop) :
    (∀ i j, P (full Y i j)) ↔
      (∀ i j, P (Y.1 i j)) ∧ (∀ i, P (Y.2.1 i)) ∧ (∀ j, P (Y.2.2.1 j)) ∧ P Y.2.2.2 := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inl j))
    · simpa [full] using h (finSumFinEquiv (Sum.inr (0 : Fin 1))) (finSumFinEquiv (Sum.inr (0 : Fin 1)))
  · rintro ⟨h1, h2, h3, h4⟩ i j
    simp only [full, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b
    · simpa using h1 a b
    · simpa using h2 a
    · simpa using h3 b
    · simpa using h4

/- English proof (translation)
Establish `hA : (∀ i j, ‖full X.toGl i j‖ ≤ 1) ↔ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1`. Rewrite using `[forall_full_entries_iff X.toGl (fun x => ‖x‖ ≤ 1)]`. Simplify using `only [Hn.toGl, Pi.star_apply, Unram.norm_star (F := F), norm_algebraMap']`. The claim follows by propositional logic. Establish `hb : ∀ i, ‖(ν • eL r E) i‖ ≤ 1`.

Introduce `i`. Distinguish the cases in `hi : i = Fin.last r`. Substitute `hi` using the available equality. Simplify `hν` using `[eL]`. Simplify using `[eL, Pi.single_eq_of_ne hi]`.

Unfold `unitU`. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]`. Establish `e : ((∀ i j, ‖(liftH X ν l).1.1 i j‖ ≤ 1) ∧ (∀ i, ‖(liftH X ν l).2.1 i‖ ≤ 1) ∧ ‖(liftH X ν l).2.2‖ ≤ 1) ↔ (‖l‖ ≤ 1 ∧ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1)`. Express the relevant statement in the definitionally equal form `((∀ i j, ‖full X.toGl i j‖ ≤ 1) ∧ (∀ i, ‖(ν • eL r E) i‖ ≤ 1) ∧ ‖l‖ ≤ 1) ↔ _`. Rewrite using `[hA]`.

Conclude with `⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hb, h.1⟩⟩`. Simplify using `only [e]`. Apply the tactic sequence `by_cases h1 : ‖l‖ ≤ 1 <;>`. Apply the tactic sequence `by_cases h2 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 <;>`. Simplify using `only [h1, h2, if_true, if_false, true_and, false_and, and_self, mul_one, mul_zero, zero_mul, implies_true]`.
-/
theorem unitU_liftH_of_norm_le_one {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ ≤ 1) :
    unitU (r + 1) F E (liftH X ν l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitU r F E X := by
  classical
  have hA : (∀ i j, ‖full X.toGl i j‖ ≤ 1) ↔
      (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 := by
    rw [forall_full_entries_iff X.toGl (fun x => ‖x‖ ≤ 1)]
    simp only [Hn.toGl, Pi.star_apply, Unram.norm_star (F := F), norm_algebraMap']
    tauto
  have hb : ∀ i, ‖(ν • eL r E) i‖ ≤ 1 := by
    intro i
    by_cases hi : i = Fin.last r
    · subst hi; simpa [eL] using hν
    · simp [eL, Pi.single_eq_of_ne hi]
  unfold unitU
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e : ((∀ i j, ‖(liftH X ν l).1.1 i j‖ ≤ 1) ∧ (∀ i, ‖(liftH X ν l).2.1 i‖ ≤ 1) ∧ ‖(liftH X ν l).2.2‖ ≤ 1) ↔
      (‖l‖ ≤ 1 ∧ (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1) := by
    change ((∀ i j, ‖full X.toGl i j‖ ≤ 1) ∧ (∀ i, ‖(ν • eL r E) i‖ ≤ 1) ∧ ‖l‖ ≤ 1) ↔ _
    rw [hA]
    exact ⟨fun h => ⟨h.2.2, h.1⟩, fun h => ⟨h.2, hb, h.1⟩⟩
  simp only [e]
  by_cases h1 : ‖l‖ ≤ 1 <;>
    by_cases h2 : (∀ i j, ‖X.1.1 i j‖ ≤ 1) ∧ (∀ i, ‖X.2.1 i‖ ≤ 1) ∧ ‖X.2.2‖ ≤ 1 <;>
    simp only [h1, h2, if_true, if_false, true_and, false_and, and_self, mul_one, mul_zero, zero_mul, implies_true]

end GlobalTheory.JR.Step
