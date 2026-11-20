import Formalism.WachLatticeTwists.WachProductBases.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Finset

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Chain the equalities or inequalities of the calculation. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem invariant_basis_average : InvariantBasisAverage := by
  intro A _ Δ _ _ _ N _ _ κ _ b ρ π hmul hone hsl hπ hcard htriv
  classical
  obtain ⟨r, hr⟩ := hcard.exists_left_inv
  have hnat : ∀ (d : Δ) (m : ℕ), d • (m : A) = (m : A) :=
    fun d m => map_natCast (MulSemiringAction.toRingHom Δ A d) m
  have hrinv : ∀ d : Δ, d • r = r := by
    intro d
    have h1 : (d • r) * ((Fintype.card Δ : ℕ) : A) = 1 := by
      have := congrArg (fun a => d • a) hr
      simpa [smul_mul', hnat] using this
    calc d • r = (d • r) * (r * ((Fintype.card Δ : ℕ) : A)) := by rw [hr, mul_one]
      _ = ((d • r) * ((Fintype.card Δ : ℕ) : A)) * r := by ring
      _ = r := by rw [h1, one_mul]
  let b' : κ → N := fun k => r • ∑ d, ρ d (b k)
  have hinv : ∀ d k, ρ d (b' k) = b' k := by
    intro d k
    simp only [b']
    rw [hsl, hrinv, map_sum]
    congr 1
    simp only [← hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  have hcong : ∀ k, ∃ y, b k = b' k - π • y := by
    intro k
    choose x' hx' using fun d => htriv d (b k)
    refine ⟨r • ∑ d, x' d, ?_⟩
    have h1 : ∑ d, ρ d (b k) = ((Fintype.card Δ : ℕ) : A) • b k + π • ∑ d, x' d := by
      rw [smul_sum, Nat.cast_smul_eq_nsmul, ← card_univ, ← sum_const, ← sum_add_distrib]
      refine sum_congr rfl fun d _ => ?_
      rw [← hx' d]; abel
    simp only [b']
    rw [h1, smul_add, smul_smul, hr, one_smul, smul_comm r π]
    abel
  have hspan : (⊤ : Submodule A N) ≤ Submodule.span A (Set.range b') := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {π})
      (Module.Finite.of_basis b).fg_top
    · rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hπ
    · rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := hcong k
      rw [hy]
      refine Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        (Submodule.mem_sup_right ?_)
      rw [b.span_eq]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top
  let f : N →ₗ[A] N := b.constr A b'
  have hf : ∀ k, f (b k) = b' k := fun k => b.constr_basis A b' k
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, b.constr_range]
    exact hspan
  haveI : Module.Finite A N := Module.Finite.of_basis b
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hsurj
  let e : N ≃ₗ[A] N := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨b.map e, fun d k => ?_⟩
  have : (b.map e) k = b' k := by
    rw [Module.Basis.map_apply]
    exact hf k
  rw [this]
  exact hinv d k

end Formalism.RepresentationBoundsCohomology.N1
