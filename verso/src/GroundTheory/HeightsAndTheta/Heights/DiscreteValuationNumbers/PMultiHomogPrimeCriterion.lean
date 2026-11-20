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
Introduce `a b h`. Use function extensionality and compare the values at `k`. Use `congrFun (congrArg ofLex h) (Fintype.equivFin K k)` as an intermediate fact. Express the relevant statement in the definitionally equal form `a ((Fintype.equivFin K).symm (Fintype.equivFin K k)) = b ((Fintype.equivFin K).symm (Fintype.equivFin K k)) at this`. Simplify using `using this`.
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
Introduce `i`. Use `⟨fun k => ofLex i (Fintype.equivFin K k), ?_⟩` and prove the remaining obligations. Use `show toLex _ = i`. Rewrite using `[← toLex_ofLex i]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
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
Simplify using `only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]`.
-/
lemma weight_lexDeg (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexDeg ∘ blockWeight ι) d = lexDeg (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, Function.comp_apply]

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [coeff_weightedHomogeneousComponent, weight_lexDeg, lexDeg_injective.eq_iff]`.
-/
lemma component_lexDeg (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (lexDeg ∘ blockWeight ι) (lexDeg b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexDeg, lexDeg_injective.eq_iff]

/- English proof (translation)
Take `⟨b, rfl⟩` from `lexDeg_surjective i`. Use `⟨b, fun d hd => ?_⟩` and prove the remaining obligations. Establish `h` using `hx hd`. Rewrite `h` using `[weight_lexDeg]`. Conclude with `lexDeg_injective h`.
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
Establish `hfin` using `weightedHomogeneousComponent_finsupp (w := w) r`. Use `conv_lhs => rw [← sum_weightedHomogeneousComponent w r, finsum_eq_sum _ hfin]`. Rewrite using `[DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_eq_single i]`. Conclude with `DirectSum.decompose_of_mem_same _ (weightedHomogeneousComponent_mem w r i)`. Introduce `m _ hm`.

Conclude with `DirectSum.decompose_of_mem_ne _ (weightedHomogeneousComponent_mem w r m) hm`. Introduce `hi`. Establish `h0 : weightedHomogeneousComponent w i r = 0`. Assume the negation of the conclusion as `h`. Conclude with `hi ((Set.Finite.mem_toFinset hfin).2 h)`.

Rewrite using `[h0, DirectSum.decompose_zero]`. Both sides reduce to the same expression.
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
Introduce `R _ K _ _ ι Q hQ hne hform`. Use `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem (𝒜 := weightedHomogeneousSubmodule R (lexDeg ∘ blockWeight ι)) ?_ hne ?_` and prove the remaining obligations. Introduce `i r hr`. Take `⟨b, rfl⟩` from `lexDeg_surjective i`. Rewrite using `[coe_decompose, component_lexDeg]`.

Conclude with `hQ r hr b`. Introduce and unpack `x y ⟨i, hx⟩ ⟨j, hy⟩ hxy`. Take `⟨sa, ha⟩` from `isMultiHomog_of_lex hx`. Take `⟨sb, hb⟩` from `isMultiHomog_of_lex hy`. Conclude with `hform x y sa sb ha hb hxy`.
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
