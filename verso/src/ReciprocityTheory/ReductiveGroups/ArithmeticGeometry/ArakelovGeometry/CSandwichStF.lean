import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem alphaMat_ker {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {N r : ℕ}
    {b : Fin r → MvPolynomial (Ix κ) ℚ} (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ)
    (hli : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l))
    (M : Matrix (Fin r) (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) ℤ)
    (hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) =
      aeval x (prodForm e (adtEnum D N (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)))
    (u : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℤ) (hu : M *ᵥ u = 0) :
    u = 0 := by
  classical
  let P : Fin (projDeg x e) → Ω := fun l =>
    ∑ i, (u (finProdFinEquiv (l, i)) : Ω) * ∏ t, (x ∘ e) t ^ adtEnum D N i t
  have hcol : ∀ j, ∑ p, (u p : Ω) * ((M j p : Ω) * aeval x (b j)) = ((M *ᵥ u) j : Ω) * aeval x (b j) := by
    intro j
    simp only [Matrix.mulVec, dotProduct]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hs : ∑ p, (u p : Ω) * aeval x (prodForm e (adtEnum D N (finProdFinEquiv.symm p).2)
      (H (finProdFinEquiv.symm p).1)) = 0 := by
    simp_rw [← hM, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hcol, hu]
    simp
  have h0 : ∑ l, P l * aeval x (H l) = 0 := by
    rw [← Equiv.sum_comp finProdFinEquiv] at hs
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, aeval_prodForm] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hP : ∀ l, P l ∈ sec ℤ (x ∘ e) N := by
    intro l
    refine ⟨∑ i, (u (finProdFinEquiv (l, i))) • monoZ (adtEnum D N i), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (monoZ_isHomogeneous (adtEnum_sum D N i)))
    · simp [P, map_sum, aeval_monoZ, zsmul_eq_mul]
  have hPz := alpha_injective x e hfr.isRatProjFrame (fun l => aeval x (H l)) hli P hP h0
  funext p
  obtain ⟨⟨l, i⟩, rfl⟩ := finProdFinEquiv.surjective p
  have h1 := eq_zero_of_sum_mono hfr.free (fun i => u (finProdFinEquiv (l, i))) (congrFun hPz l)
  simpa using congrFun h1 i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
