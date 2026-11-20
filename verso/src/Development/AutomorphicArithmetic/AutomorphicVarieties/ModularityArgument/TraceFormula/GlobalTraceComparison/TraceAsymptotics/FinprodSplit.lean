import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Introduce `α S Z T F hZ hT hd h1`. Establish `key : ∏ᶠ w ∈ S, F w = ∏ w ∈ T ∪ Z, F w`. Apply `finprod_mem_eq_prod_of_inter_mulSupport_eq` to reduce the goal to its premises. Use extensionality with `w`. Simplify using `only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_union, Set.mem_union, Finset.mem_coe]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hS, hF⟩`. Use `⟨?_, hF⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `hF (h1 w hS (fun h => hn (Or.inr h)) (fun h => hn (Or.inl h)))`.

Introduce and unpack `⟨hw | hw, hF⟩`. Conclude with `⟨hT w hw, hF⟩`. Conclude with `⟨hZ w hw, hF⟩`. Rewrite using `[key, Finset.prod_union hd, mul_comm]`.
-/
theorem finprodSplit : FinprodSplit := by
  intro α S Z T F hZ hT hd h1
  classical
  have key : ∏ᶠ w ∈ S, F w = ∏ w ∈ T ∪ Z, F w := by
    apply finprod_mem_eq_prod_of_inter_mulSupport_eq
    ext w
    simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.coe_union, Set.mem_union,
      Finset.mem_coe]
    constructor
    · rintro ⟨hS, hF⟩
      refine ⟨?_, hF⟩
      by_contra hn
      exact hF (h1 w hS (fun h => hn (Or.inr h)) (fun h => hn (Or.inl h)))
    · rintro ⟨hw | hw, hF⟩
      · exact ⟨hT w hw, hF⟩
      · exact ⟨hZ w hw, hF⟩
  rw [key, Finset.prod_union hd, mul_comm]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
