import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuot

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem finite_not_le_one (a : K) : {i | ¬ C.v i a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    simp
  · refine (C.fin a ha).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro h
    exact hi (le_of_eq h)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_not_mapsTo {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {n m : ℕ} (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin m) K V')
    (f : V →ₗ[K] V') :
    {i | ¬ ∀ x, (∀ q, C.v i (b.repr x q) ≤ 1) → ∀ q, C.v i (b'.repr (f x) q) ≤ 1}.Finite := by
  classical
  refine (Set.finite_iUnion fun q : Fin m => Set.finite_iUnion fun r : Fin n =>
    finite_not_le_one C (b'.repr (f (b r)) q)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  apply hi
  intro x hx q
  have hx' : f x = ∑ r, b.repr x r • f (b r) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul]
  rw [hx', map_sum, Finsupp.finset_sum_apply]
  refine (C.v i).map_sum_le fun r _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, (C.v i).map_mul]
  exact mul_le_one' (hx r) (hcon q r)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isBun_sub_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V),
    IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  unfold IsBun at hL ⊢
  obtain ⟨hloc, b0, hb0⟩ := hL
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective W.mkQ W.range_mkQ
  refine ⟨⟨fun i => ?_, Module.finBasis K W, ?_⟩, ⟨fun i => ?_, Module.finBasis K (V ⧸ W), ?_⟩⟩
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, hW, -, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bW, hW⟩
  · refine ((hb0.union (finite_not_mapsTo C (Module.finBasis K W) b0 W.subtype)).union
      (finite_not_mapsTo C b0 (Module.finBasis K W) g)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro w
    show (w : V) ∈ L i ↔ _
    rw [h1]
    have hgw : g (w : V) = w := by simpa using LinearMap.congr_fun hg w
    constructor
    · intro hw q
      have hq := h3 (w : V) hw q
      rwa [hgw] at hq
    · intro hw q
      exact h2 w hw q
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, -, hQ, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bQ, hQ⟩
  · refine ((hb0.union (finite_not_mapsTo C b0 (Module.finBasis K (V ⧸ W)) W.mkQ)).union
      (finite_not_mapsTo C (Module.finBasis K (V ⧸ W)) b0 s)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro y
    show y ∈ (L i).map W.mkQ.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ q
      exact h2 x ((h1 x).1 hx) q
    · intro hy
      have hsy : W.mkQ (s y) = y := by simpa using LinearMap.congr_fun hs y
      exact ⟨s y, (h1 (s y)).2 (h3 y hy), hsy⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuot
