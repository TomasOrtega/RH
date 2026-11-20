import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BoundInf
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ a`. Establish `hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a))`. Use `Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun g : GL (Fin a) (Cinf E) => (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))`. Conclude with `(Units.continuous_val.mul continuous_const).mul Units.continuous_val.star`.

Use `⟨hcont, fun K hK hKc => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)`. Establish `hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C}`. Establish `h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C)` using `isCompact_closedBall _ _`. Establish `e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C}`.

Use extensionality with `m`. Simplify using the standard rewrite rules. Rewrite `h` using `[e]`. Conclude with `h`. Establish `hT` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))`.

Use `hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩` and prove the remaining obligations. Conclude with `hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)`. Use `hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_` and prove the remaining obligations. Establish `e : sand g⁻¹ (sand g (hOne E a)) = hOne E a`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Set.mem_insert _ _`.
-/
theorem UpperTheory.V.Cj.A.sandCpt :
    SandCpt := by
  intro E _ _ a
  have hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) := by
    refine Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _
    change Continuous fun g : GL (Fin a) (Cinf E) =>
      (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))
    exact (Units.continuous_val.mul continuous_const).mul Units.continuous_val.star
  refine ⟨hcont, fun K hK hKc => ?_⟩
  obtain ⟨C, hC⟩ := boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)
  have hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C} := by
    have h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C) := isCompact_closedBall _ _
    have e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C} := by
      ext m; simp
    rw [e] at h
    exact h
  have hT := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  refine hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩
  · exact hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)
  · refine hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_
    have e : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e]
    exact Set.mem_insert _ _
