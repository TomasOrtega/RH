import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace MultiHomogPrimeCriterion

variable {K : Type} [Fintype K] [DecidableEq K]

def lexDeg : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex fun j => b ((Fintype.equivFin K).symm j)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq K] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify to obtain the desired conclusion from the available facts.
-/
lemma lexDeg_injective : Function.Injective (lexDeg (K := K)) := by
  intro a b h
  funext k
  have := congrFun (congrArg ofLex h) (Fintype.equivFin K k)
  change a ((Fintype.equivFin K).symm (Fintype.equivFin K k)) =
    b ((Fintype.equivFin K).symm (Fintype.equivFin K k)) at this
  simpa using this

omit [DecidableEq K] in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
lemma lexDeg_surjective : Function.Surjective (lexDeg (K := K)) := by
  intro i
  refine ⟨fun k => ofLex i (Fintype.equivFin K k), ?_⟩
  show toLex _ = i
  rw [← toLex_ofLex i]
  congr 1
  funext j
  simp

variable {ι : K → Type} {R : Type u} [CommRing R]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma weight_lexDeg (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
lemma component_lexDeg (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (lexDeg ∘ blockWeight ι) (lexDeg b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexDeg, lexDeg_injective.eq_iff]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma isMultiHomog_of_lex {x : MRing ι R} {i : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : IsWeightedHomogeneous (lexDeg ∘ blockWeight ι) x i) : ∃ s, IsMultiHomog x s := by
  obtain ⟨b, rfl⟩ := lexDeg_surjective i
  refine ⟨b, fun d hd => ?_⟩
  have h := hx hd
  rw [weight_lexDeg] at h
  exact lexDeg_injective h

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma coe_decompose {σ M : Type*} [AddCommMonoid M] {_ : DecidableEq M} (w : σ → M)
    [GradedRing (weightedHomogeneousSubmodule R w)] (r : MvPolynomial σ R) (i : M) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) r i : MvPolynomial σ R) =
      weightedHomogeneousComponent w i r := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := w) r
  conv_lhs => rw [← sum_weightedHomogeneousComponent w r, finsum_eq_sum _ hfin]
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum,
    Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same _ (weightedHomogeneousComponent_mem w r i)
  · intro m _ hm
    exact DirectSum.decompose_of_mem_ne _ (weightedHomogeneousComponent_mem w r m) hm
  · intro hi
    have h0 : weightedHomogeneousComponent w i r = 0 := by
      by_contra h
      exact hi ((Set.Finite.mem_toFinset hfin).2 h)
    rw [h0, DirectSum.decompose_zero]
    rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem proof : MultiHomogPrimeCriterion.Statement := by
  intro R _ K _ _ ι Q hQ hne hform
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule R (lexDeg ∘ blockWeight ι)) ?_ hne ?_
  · intro i r hr
    obtain ⟨b, rfl⟩ := lexDeg_surjective i
    rw [coe_decompose, component_lexDeg]
    exact hQ r hr b
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    obtain ⟨sa, ha⟩ := isMultiHomog_of_lex hx
    obtain ⟨sb, hb⟩ := isMultiHomog_of_lex hy
    exact hform x y sa sb ha hb hxy

end MultiHomogPrimeCriterion

end

end GroundTheory.Heights₂.Heights.NumbersDVR
