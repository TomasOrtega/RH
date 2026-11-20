import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open Algebra GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ratioField_eq_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have key : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq]
      have h0 := hc p.1
      by_cases hq0 : y q = 0
      · simp [hq0]
      · field_simp
    rw [key]
    exact div_mem hp hq

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem ringKrullDim_coord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI hP : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime (mConeMap y)
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.full (MRing ι ⧸ mCoordIdeal y)
    (algebraMap_injective _ (horizontal y))
  have hne : ∀ k, ∃ i, ratioPtL y c ⟨k, i⟩ ≠ 0 := by
    intro k
    refine ⟨c k, fun h0 => ?_⟩
    have h1 := congrArg Subtype.val h0
    change ratioPt y c ⟨k, c k⟩ = 0 at h1
    simp [ratioPt, hc k] at h1
  have htr := GroundTheory.Heights₂.Heights.ConeTrdeg.full K ι (ratioField y c) (ratioPtL y c)
    (birational y c hc) hne (horizontal _)
  rw [mCoordIdeal_ratioPtL y c hc] at htr
  rw [hdim, htr, ratioField_eq_blockFnField y c hc]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trdeg_eq_of_le_of_isAlgebraic {L₁ L₂ : IntermediateField ℚ Ω} (h : L₁ ≤ L₂)
    (halg : ∀ t ∈ L₂, IsAlgebraic L₁ t) : Algebra.trdeg ℤ L₂ = Algebra.trdeg ℤ L₁ := by
  letI : Algebra L₁ L₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let f : L₂ →ₐ[L₁] Ω :=
    { toRingHom := L₂.val.toRingHom
      commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic L₁ L₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff f Subtype.val_injective).mp (halg x x.2)⟩
  have h0 : trdeg L₁ L₂ = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq (R := ℤ) (S := L₁) (A := L₂), h0, add_zero]

end Dim

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable.

Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. It suffices to derive a contradiction.

Establish an intermediate fact. Treat this case separately. Put the expressions in a common number system so they can be compared. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem isArithVar_of_isAlgebraic_image (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type)
    [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type)
    [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ) (hv : IsBlockMap κ v)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (hz : IsArithVar (mCoordIdeal (y ∘ v)) d)
    (halg : ∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) : IsArithVar (mCoordIdeal y) d := by
  classical
  obtain ⟨hK, -, -, hdz⟩ := hz
  obtain ⟨hκ, -, hfst, hsurj⟩ := hv
  choose c' hc' using hy
  have hcv : ∀ k : K, ∃ i : ι k, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨⟨k', i⟩, hp⟩ := hsurj ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h2 : k' = k := by
      apply hκ
      have h3 := hfst ⟨k', i⟩
      rw [hp] at h3
      exact h3.symm
    subst h2
    exact ⟨i, fun h0 => hc' _ (by rw [← hp]; exact h0)⟩
  choose c hc using hcv
  have e1 := hdz.symm.trans (ringKrullDim_coord (y ∘ v) c hc)
  have hle : blockFnField (y ∘ v) ≤ blockFnField y := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hfst, hfst, hpq], rfl⟩
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg
  unfold IsArithVar IsMultiProjPrime
  refine ⟨⟨κ hK.some⟩, ⟨RingHom.ker_isPrime (mConeMap y), isMultiHomogIdeal y, relevant y c' hc'⟩,
    horizontal y, ?_⟩
  rw [ringKrullDim_coord y c' hc', htr]
  generalize Algebra.trdeg ℤ ↥(blockFnField (y ∘ v)) = T at e1 ⊢
  simp only [map_add, map_natCast] at e1 ⊢
  generalize Cardinal.toENat T = e at e1 ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h5 : ((d + Fintype.card K : ℕ) : ℕ∞) = ⊤ := by exact_mod_cast e1
    exact ENat.natCast_ne_top _ h5
  | coe m =>
    norm_cast at e1 ⊢
    omega

end GlobalTheory.CompanionTheory.Ar.Cmp
