import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.Published

open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Establish `hrange : (U : Set X) ⊆ Set.range π`. Introduce `y hy`. Take `⟨x, hx⟩` from `(ConcreteCategory.bijective_of_isIso ((π ∣_ U).base)).2 ⟨y, hy⟩`. Use `⟨x.1, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hx` as an intermediate fact.

Simplify `this` using `[morphismRestrict_base_coe]`. Establish `hgen : π (genericPoint X') = genericPoint X`. Establish `h1` using `(genericPoint_spec X').image π.continuous`. Establish `hdense : closure (Set.range π) = Set.univ`. Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises.

Rewrite using `[← (U.isOpen.dense hU).closure_eq]`. Conclude with `closure_mono hrange`. Rewrite `h1` using `[Set.image_univ, hdense]`. Conclude with `h1.eq (genericPoint_spec X)`. Use `⟨hgen, ?_⟩` and prove the remaining obligations.

Establish `hmem : genericPoint X' ∈ π ⁻¹ᵁ U` using `by show π (genericPoint X') ∈ U`. Rewrite using `[hgen]`. Conclude with `((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : genericPoint X' ∈ Set.range (π ⁻¹ᵁ U).ι := by`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hmem`. Establish `h1` using `_root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ∣_ U) U.ι x`. Establish `h2` using `_root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ⁻¹ᵁ U).ι π x`. Rewrite `h1` using `[morphismRestrict_ι, h2, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ⁻¹ᵁ U).ι, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion U.ι, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ∣_ U), hx]`. Simplify using `using h1`.
-/
theorem _root_.GlobalTheory.Published.generic_of_isIso_restrict {X X' : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] (π : X' ⟶ X) (U : X.Opens)
    (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)] :
    π (genericPoint X') = genericPoint X ∧ π.residueDegree (genericPoint X') = 1 := by
  have hrange : (U : Set X) ⊆ Set.range π := by
    intro y hy
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((π ∣_ U).base)).2 ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    have := congrArg Subtype.val hx
    simpa [morphismRestrict_base_coe] using this
  have hgen : π (genericPoint X') = genericPoint X := by
    have h1 := (genericPoint_spec X').image π.continuous
    have hdense : closure (Set.range π) = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← (U.isOpen.dense hU).closure_eq]
      exact closure_mono hrange
    rw [Set.image_univ, hdense] at h1
    exact h1.eq (genericPoint_spec X)
  refine ⟨hgen, ?_⟩
  have hmem : genericPoint X' ∈ π ⁻¹ᵁ U := by
    show π (genericPoint X') ∈ U
    rw [hgen]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨x, hx⟩ : genericPoint X' ∈ Set.range (π ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]; exact hmem
  have h1 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ∣_ U) U.ι x
  have h2 := _root_.GlobalTheory.CurveDegreesCompare.residueDegree_comp (π ⁻¹ᵁ U).ι π x
  rw [morphismRestrict_ι, h2, _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ⁻¹ᵁ U).ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion U.ι,
    _root_.GlobalTheory.CurveDegreesCompare.residueDegree_of_isOpenImmersion (π ∣_ U), hx] at h1
  simpa using h1

open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Introduce `k _ X X' _ _ p p' D hp hp' _ _ π hπ U hU hiso L a hL`. Take `⟨hgen, hdeg⟩` from `_root_.GlobalTheory.Published.generic_of_isIso_restrict π U hU`. Use `(H k X X' p p' D hp hp' π hπ hgen (by rw [hdeg]; exact one_ne_zero)).1 L a hL` as an intermediate fact. Simplify `this` using `[hdeg]`.
-/
theorem _root_.GlobalTheory.Published.arBirational_of_arProj (H : _root_.GlobalTheory.Published.ArProj) :
    _root_.GlobalTheory.Published.ArBirational := by
  intro k _ X X' _ _ p p' D hp hp' _ _ π hπ U hU hiso L a hL
  obtain ⟨hgen, hdeg⟩ := _root_.GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have := (H k X X' p p' D hp hp' π hπ hgen (by rw [hdeg]; exact one_ne_zero)).1 L a hL
  simpa [hdeg] using this

end GlobalTheory.Published
