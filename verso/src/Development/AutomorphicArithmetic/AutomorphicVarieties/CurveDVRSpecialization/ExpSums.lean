import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.Combinatorics.HalesJewett
import Mathlib.LinearAlgebra.Vandermonde

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pr.expSums :
    UpperTheory.V.Pr.ExpSums := by
  intro κ ι σ _ _ _ α c hα hc
  classical
  by_contra hne
  push Not at hne
  choose C hC using hne
  obtain ⟨a, ha, b, s, hs⟩ :=
    Combinatorics.exists_mono_homothetic_copy (Finset.range (Fintype.card ι)) C
  let e := (Fintype.equivFin ι).symm
  have hinj : Function.Injective fun j : Fin (Fintype.card ι) => ((α s (e j) : κˣ) : κ) ^ a := by
    intro i j hij
    by_contra h
    refine hα s (e i) (e j) (fun h' => h (e.injective h')) a ha ?_
    apply Units.ext
    simpa using hij
  have h0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (v := fun j => c s (e j) * ((α s (e j) : κˣ) : κ) ^ b) hinj (by
      intro i
      have h1 := hC (a • (i : ℕ) + b)
      rw [hs i (Finset.mem_range.2 i.2), ← e.sum_comp] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, pow_add, pow_mul]
      ring)
  obtain ⟨i, hi⟩ := hc s
  have h2 := congrFun h0 (e.symm i)
  simp only [Equiv.apply_symm_apply, Pi.zero_apply, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hi h2
  · exact pow_ne_zero _ (α s i).ne_zero h2
