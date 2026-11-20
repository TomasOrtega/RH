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
Rewrite using `[fnField, IntermediateField.adjoin_toSubfield]`. Unfold `IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField`. Use `congr 2`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, q, hpq, rfl⟩`. Take `⟨a, i⟩` from `p`. Take `⟨b, j⟩` from `q`. Simplify using `only at hpq`. Substitute `hpq` using the available equality.

Conclude with `⟨⟨a, i, j⟩, rfl⟩`. Introduce and unpack `⟨⟨a, i, j⟩, rfl⟩`. Conclude with `⟨⟨a, i⟩, ⟨a, j⟩, rfl, rfl⟩`.
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
Rewrite using `[← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]`.
-/
theorem trdeg_eq_of_finite (A : IntermediateField k Ω) [FiniteDimensional A Ω] : Algebra.trdeg k A = Algebra.trdeg k Ω := by
  rw [← trdeg_add_eq k A (A := Ω), trdeg_eq_zero (R := A) (A := Ω), add_zero]

/- English proof (translation)
Take `⟨hnz, hfin, htr⟩` from `h`. Establish `hcone` using `ConeTrdegFnField.proof k Ω (algebraMap k Ω).injective K ι y hnz`. Establish `hset : ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω) = ((fnField k y : IntermediateField k Ω) : Set Ω)`. Rewrite using `[← fnField_toSubfield k y]`. Both sides reduce to the same expression.

Establish `hadj : Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) = Algebra.trdeg k (fnField k y)`. Rewrite using `[hset]`. Establish `: Algebra.adjoin k ((fnField k y : IntermediateField k Ω) : Set Ω) = (fnField k y).toSubalgebra` using `Algebra.adjoin_eq (fnField k y).toSubalgebra`. Rewrite using `[this]`. Both sides reduce to the same expression.

Use `haveI : FiniteDimensional (fnField k y) Ω := hfin`. Establish `htr' : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = ((d + Fintype.card K : ℕ) : Cardinal)`. Establish `e : Algebra.trdeg k (MRing ι k ⧸ pointIdeal k y) = Algebra.trdeg k (Algebra.adjoin k ((IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField k y : Subfield Ω) : Set Ω)) + (Fintype.card K : Cardinal)` using `hcone`. Rewrite using `[e, hadj, trdeg_eq_of_finite k (fnField k y), htr]`. Use `push_cast`.

Both sides reduce to the same expression. Conclude with `ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (d + Fintype.card K) htr'`.
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
Introduce `k _ Ω _ _ K _ ι _ y d h`. Establish `hmp : IsMultiProjPrime (pointIdeal k y)` using `PointIdealMultiProj.proof k Ω K ι y h.1`. Establish `hdim` using `krull_pointIdeal k y d h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `hmp` and compare the differences between its conclusion and the goal.

Unfold `FieldNumbers.relDim`. Rewrite using `[hdim]`. Establish `e : (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ)) = (d : ℤ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `(WithBot.some (WithTop.some (((d + Fintype.card K : ℕ) : ℤ) - (Fintype.card K : ℤ))) : WithBot (WithTop ℤ)) = ((d : ℤ) : WithBot (WithTop ℤ))`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `⟨?_, hdim⟩` and prove the remaining obligations. Conclude with `(Bridge.isMultiProjPrime_iff _).1 hmp`.
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
