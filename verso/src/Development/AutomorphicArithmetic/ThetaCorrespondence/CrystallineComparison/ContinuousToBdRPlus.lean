import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Topology

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem toBdRPlus_mem_nhd (n k : ℕ) (y : Acris p R) :
    Acris.toBdRPlus p R ((p : Acris p R) ^ (n + k) * y) ∈ BdRPlus.nhd p R (n, k) := by
  obtain ⟨b, hb⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n y)
  refine ⟨b, ?_⟩
  have h1 := congrArg Subtype.val hb
  simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1
  simp only [map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, pow_add]
  rw [mul_comm ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n), mul_assoc, h1]
  congr 1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem continuous_toBdRPlus : Continuous (Acris.toBdRPlus p R) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, (Ideal.hasBasis_nhds_zero_adic (span {(p : Acris p R)})).tendsto_iff
    (BdRPlus.hasBasis_nhds_zero p R)]
  intro i _
  refine ⟨i.1 + i.2, trivial, fun x hx => ?_⟩
  rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  exact toBdRPlus_mem_nhd i.1 i.2 y

end Formalism.BasicNotions.CmpTie.Incl
