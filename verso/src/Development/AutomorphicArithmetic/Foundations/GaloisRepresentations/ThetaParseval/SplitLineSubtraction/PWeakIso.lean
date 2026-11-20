import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TP.Sub.weakIso_holds :
    SatAE → WeakIso := by
  intro hA E Ω _ _ _ _ _ _ l _ ι a U hU r r' hr hr'
  obtain ⟨hc, hs, he⟩ := hr
  obtain ⟨hc', hs', he'⟩ := hr'
  have hev := he.and (he'.and (hA E a U hU))
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (GlobalTheory.SplitAttUniq.dense_splitFrobInv_away E Ω l (Fact.out) _ (Filter.eventually_cofinite.1 hev)) ?_
  rintro g ⟨w, hw, hsp, hl, A, hP, hF⟩
  obtain ⟨h1, h2, h3⟩ := not_not.1 hw
  obtain ⟨B, hB⟩ := h3 hsp
  have e1 := ((h1 hsp B hB) A hP).2 g⁻¹ hF
  have e2 := ((h2 hsp B hB) A hP).2 g⁻¹ hF
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
