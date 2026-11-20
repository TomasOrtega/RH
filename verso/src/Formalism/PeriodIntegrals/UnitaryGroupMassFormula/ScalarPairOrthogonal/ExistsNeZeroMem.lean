import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.MemThPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton

noncomputable section

open scoped Classical

namespace PI.ScalarPairDr.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem exists_ne_zero_mem (D : D7) (j : ℤ) :
    ∃ x : D.host.E, x ≠ 0 ∧ x ∈ (ddS D ^ j : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h : ddS D ^ j ≠ 0 := zpow_ne_zero j (ddS_ne_zero D)
  by_contra hne
  push_neg at hne
  apply h
  rw [FractionalIdeal.eq_zero_iff]
  intro x hx
  by_contra hx0
  exact hne x hx0 hx

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem X_le_spanE_XS (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    F0.X ≤ spanE (VS D) (XS D F0) := by
  unfold FlagG.X spanE
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem D (-((D.R.rS : ℤ) - (a : ℕ)))
  have hmem : x • F0.e a ∈ (XS D F0 : Set (VS D).V) := by
    unfold XS
    exact Submodule.subset_span ⟨a, x, hx, rfl⟩
  have h2 : x • F0.e a ∈ Submodule.span D.host.E (XS D F0 : Set (VS D).V) := Submodule.subset_span hmem
  have h3 := Submodule.smul_mem _ x⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hx0, one_smul] at h3

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem Tu_ne_zero (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
  unfold Tu
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem scalarDr (D : D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' := by
  intro F0 what₂ hrows Λ hΛ x y hGx hGy β _hpair hs hsc
  have hrow := hrows.1 Λ hΛ
  have hXF : Xsp (lf D F0) ≤ spanE (VS D) (XLam Λ (lf D F0)) := by
    rw [hrow.2.2]
    exact X_le_spanE_XS D F0
  have hXx : Xsp x.1 ≤ spanE (VS D) (XLam Λ x.1) := by
    rw [x.2.2.2.2]
    exact X_le_spanE_XS D x.1.fl
  have hXy : Xsp y.1 ≤ spanE (VS D) (XLam Λ y.1) := by
    rw [y.2.2.2.2]
    exact X_le_spanE_XS D y.1.fl
  exact core Λ D.R.k (lf D F0) x.1 y.1 β rfl x.2.1.2 y.2.1.2 hXF hXx hXy
    (PI.UnitaryGroupMassFormula.BetaLUniq.finrank_hS D) (Tu_ne_zero D u) hGx hGy hs hsc

end D7

end PI.ScalarPairDr.W
