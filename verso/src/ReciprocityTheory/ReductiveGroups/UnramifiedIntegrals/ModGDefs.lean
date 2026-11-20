import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.NeutralLocalFields.HilbertClassField

noncomputable section
open scoped BigOperators Classical
open NumberField IsDedekindDomain Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def sqD (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqD_sq (d : ℕ) : sqD d ^ 2 = -(d : ℂ) := by
  unfold sqD
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

def KQ (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqD d}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem sqD_isIntegral (d : ℕ) : IsIntegral ℚ (sqD d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [sqD_sq]

scoped instance KQ_numberField (d : ℕ) : NumberField (KQ d) where
  to_charZero := inferInstance
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (sqD_isIntegral d)

def sqK (d : ℕ) : KQ d := ⟨sqD d, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

abbrev Om (d : ℕ) : IntermediateField (KQ d) ℂ := algebraicClosure (KQ d) ℂ

def Aio (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) : ValuationSubring (Om d) :=
  ((NormedField.valuation (K := ℂ_[l])).valuationSubring).comap
    ((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ))

def InertiaEl {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) : Prop :=
  g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ∈ A.nonunits

end ReciprocityTheory.ChartRestriction.L1
