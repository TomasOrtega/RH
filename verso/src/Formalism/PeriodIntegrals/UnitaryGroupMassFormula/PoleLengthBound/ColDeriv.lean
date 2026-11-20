import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Vanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem u_eq_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) {u : Fin G.N → OsK X la G.w}
    (hu : uSpec G la u) (col : Fin G.N) : u col = toOsK X la G.w (PoleLengthBounds.wfr G la col) := by
  obtain ⟨f, hf, hfu⟩ := hu col
  have : f = PoleLengthBounds.wfr G la col := by
    apply Subtype.ext
    rw [hf]
    simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]
  rw [← hfu, this]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem uC_eq_pow (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) {k : ℕ}
    (α : Mon (WeightFamilies.dimY D j) k) :
    PoleLengthBounds.uC G la col α.1 = toOsK X la G.w (PoleLengthBounds.wfr G la col) ^ k := by
  have h := α.2
  rw [Finset.Nat.mem_antidiagonalTuple] at h
  rw [PoleLengthBounds.uC, Finset.prod_pow_eq_pow_sum, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem colDeriv_of (hTH : PoleLengthBounds.TaylorHasse) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ColDeriv G la := by
  classical
  intro u hu k α α' col cf
  have hx : ((yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF :=
    (yPow X la G.w α.1 • cf).2
  have h := hasse_preserves_kernel G la (colIdx D j col α'.1) _ hx
  let cf' : (Fin (WeightFamilies.dimY D j) → ℕ) → ↥(HK X la G.w wF) := fun β => if β = α.1 then cf else 0
  have hrem : (yPow X la G.w α.1 • cf : ↥(HK X la G.w wF)) -
      ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β ∈
        (Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) := by
    have : ∑ β ∈ PoleLengthBounds.mon D j k, PoleLengthBounds.ym G la β • cf' β = yPow X la G.w α.1 • cf := by
      rw [Finset.sum_eq_single α.1]
      · simp only [cf', if_pos rfl]; rfl
      · intro b _ hb; simp only [cf', if_neg hb, smul_zero]
      · intro hn; exact absurd α.2 hn
    rw [this, sub_self]
    exact Submodule.zero_mem _
  have key := hTH G la k _ cf' hrem col α'.1 α'.2 h
  rw [rD, dif_pos h]
  refine Eq.trans key ?_
  rw [uC_eq_pow G la col α', u_eq_wfr G la hu col]
  by_cases hαα : α = α'
  · subst hαα
    simp only [cf', ↓reduceIte]
  · have hne : α'.1 ≠ α.1 := fun e => hαα (Subtype.ext e.symm)
    simp only [cf', if_neg hne, if_neg hαα, map_zero, smul_zero]

end PI.PoleLengthCount
