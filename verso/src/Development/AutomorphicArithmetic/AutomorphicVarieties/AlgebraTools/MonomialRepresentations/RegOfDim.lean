import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne

open Polynomial Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities. Put the expressions in a common number system so they can be compared.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.regOfDim :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R), J ≠ ⊤ →
      ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) → J = ⊥ := by
  intro R _ _ _ J hJ hdim
  have hR := ringKrullDim_le_spanFinrank_maximalIdeal R
  have hq := ringKrullDim_quotient_le J
  have heq : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm (hdim.trans hq) hR
  have hJeq : ringKrullDim (R ⧸ J) = ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    le_antisymm (hq.trans hR) hdim
  haveI : IsRegularLocalRing R := ⟨heq⟩
  haveI := PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain R
  by_contra hne
  obtain ⟨r, hrJ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
  have hsub : Ideal.span {r} ≤ J := (Ideal.span_singleton_le_iff_mem J).2 hrJ
  have h2 : ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsub) (Ideal.Quotient.factor_surjective hsub)
  have h3 : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ J) := by
    calc ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ ringKrullDim R := h1
      _ = ringKrullDim (R ⧸ J) := by rw [hJeq, heq]
  rw [hJeq] at h3
  norm_cast at h3
  omega
