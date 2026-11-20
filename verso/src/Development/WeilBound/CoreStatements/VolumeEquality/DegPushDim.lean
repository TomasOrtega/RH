import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPointIdealMultiProj
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

noncomputable section

namespace SheetDecomposition

open ReciprocityTheory.ChartRestriction.G
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR

section

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

omit [Fintype K] [∀ b, Fintype (ι b)] in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem fnField_toSubfield (y : (Σ b, ι b) → Ω) :
    (fnField k y).toSubfield = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y := by
  rw [fnField, IntermediateField.adjoin_toSubfield]
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField
  congr 2
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only at hpq
    subst hpq
    exact ⟨⟨a, i, j⟩, rfl⟩
  · rintro ⟨⟨a, i, j⟩, rfl⟩
    exact ⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem krull_pointIdeal (y : (Σ b, ι b) → Ω) (d : ℕ) (h : IsPt k y d) [(pointIdeal k y).IsPrime] :
    ringKrullDim (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hnz, hfin, htr⟩ := h
  have hcone := ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz
  have hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω) := by
    rw [← fnField_toSubfield k y]
    rfl
  have hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y) := by
    rw [hset]
    have : Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra :=
      Algebra.adjoin_eq (fnField k y).toSubalgebra
    rw [this]
    rfl
  haveI : FiniteDimensional (fnField k y) Ω := hfin
  have htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal) := hcone
    rw [e, hadj, trdeg_eq_of_finite k (fnField k y), htr]
    push_cast
    rfl
  exact ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem ptDim : PtDim := by
  intro k _ Ω _ _ K _ ι _ y d h
  classical
  have hmp : IsMultiProjPrime (pointIdeal k y) := PointIdealMultiProj.proof k Ω K ι y h.1
  have hdim := krull_pointIdeal k y d h
  refine ⟨?_, ?_, ?_⟩
  · convert hmp
  · unfold FieldNumbers.relDim
    rw [hdim]
    have e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ) := by
      push_cast
      ring
    change (WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))
    rw [e]
    rfl
  · refine ⟨?_, hdim⟩
    exact (Bridge.isMultiProjPrime_iff _).1 hmp

end SheetDecomposition
