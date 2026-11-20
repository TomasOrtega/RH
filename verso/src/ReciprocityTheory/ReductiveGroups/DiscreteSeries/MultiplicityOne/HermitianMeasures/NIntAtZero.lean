import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.NIntStep

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Introduce `μN hH b _`. Establish `hc` using `hH.conc`. Rewrite `hc` using `[hNB k]`. Establish `hae : ∀ᵐ x ∂μN, x ∈ ({(show Mt k 0 from (1 : Matrix (Fin (2 * 0 + k + 1)) (Fin (2 * 0 + k + 1)) ℂ))} : Set (Mt k 0))`. Rewrite using `[ae_iff]`.

Conclude with `hc`. Rewrite using `[← Measure.restrict_eq_self_of_ae_mem hae, lintegral_singleton]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hH.finite_compact _ isCompact_singleton)`.
-/
theorem nIntAt_zero (hNB : NBase) (k : ℕ) : NIntAt k 0 := by
  intro μN hH b _
  have hc := hH.conc
  rw [hNB k] at hc
  have hae : ∀ᵐ x ∂μN, x ∈
      ({(show Mt k 0 from (1 : Matrix (Fin (2 * 0 + k + 1)) (Fin (2 * 0 + k + 1)) ℂ))} : Set (Mt k 0)) := by
    rw [ae_iff]
    exact hc
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_singleton]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hH.finite_compact _ isCompact_singleton)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact nIntAt_zero hNB k`. Consider the case `succ r' ih`. Establish `h` using `nIntAt_step hNR hHU hCN hHN hGL k r' ih`. Rewrite `h` using `[Nat.add_comm 1 r']`. Then use the resulting hypothesis.
-/
theorem nIntAt_all (hNB : NBase) (hNR : NRecHaar) (hHU : HaarUnique) (hCN : ClosedN) (hHN : HaarNExists)
    (hGL : GNLower) (k r : ℕ) : NIntAt k r := by
  induction r with
  | zero => exact nIntAt_zero hNB k
  | succ r' ih =>
    have h := nIntAt_step hNR hHU hCN hHN hGL k r' ih
    rwa [Nat.add_comm 1 r'] at h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
