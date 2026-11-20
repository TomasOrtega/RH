import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntMaxFinExt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem mem_maximalIdeal_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  intro l _ K _ y
  have hle : ∀ z : ↥(Loc.OL K), ‖((z : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := fun z =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (z : ↥K.1)).1 z.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hlt
    have h1 : ‖((y : ↥K.1) : PadicAlgCl l)‖ = 1 := le_antisymm (hle y) (not_lt.1 hlt)
    have hy0 : (y : ↥K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have hinv : ((y : ↥K.1)⁻¹ : ↥K.1) ∈ Loc.OL K := by
      rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
      rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
    apply hnu
    refine ⟨⟨y, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (y : ↥K.1) * (y : ↥K.1)⁻¹ = 1
      exact mul_inv_cancel₀ hy0
    · apply Subtype.ext
      show (y : ↥K.1)⁻¹ * (y : ↥K.1) = 1
      exact inv_mul_cancel₀ hy0
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    have hm : ((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l)) * ((((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l) = 1 := by
      have := congrArg (fun z : ↥(Loc.OL K) => (((z : ↥K.1)) : PadicAlgCl l)) u.mul_inv
      exact this
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    have h2 := hle ((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K))
    have h0 : 0 ≤ ‖((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l))‖ := norm_nonneg _
    nlinarith

end GlobalTheory.IntMaxFinExt
