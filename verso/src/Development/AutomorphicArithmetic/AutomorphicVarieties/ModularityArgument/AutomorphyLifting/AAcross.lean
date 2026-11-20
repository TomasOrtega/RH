import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ThruAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AIsoTwOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AUpDownOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ContOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.GalN.V

namespace UpperTheory.V.Z.Win

/- English proof (translation)
The claim follows from `thruAway plainRec`.
-/
theorem thruF : Thru false := thruAway plainRec

/- English proof (translation)
The claim follows from `aIsoTwOf flagLaws ImaginaryQuadraticEtaCharacter.winTw`.
-/
theorem aIsoTw : AIsoTw := aIsoTwOf flagLaws ImaginaryQuadraticEtaCharacter.winTw

/- English proof (translation)
The claim follows from `compatTOf h plainRec`.
-/
theorem compatT (h : RowT) : CompatT := compatTOf h plainRec

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} [IsAlgClosure F Ω]

/- English proof (translation)
The claim follows from `have k := (flagLaws F Ω l n r).1 r' e have k' := (flagLaws F Ω l n r').1 r e.symm' ⟨fun v hv u => (k.2.2 v).2 (h.1 v hv ((k'.2.2 v).1 u)), fun π hreg ha => (h.2 π hreg (attC_iso e.symm' ha)).imp fun _ ht v hv => ht v (hv.imp id (k'.2.2 v).2)⟩`.
-/
theorem WitA.iso [IsCMField F] (e : RepIso r r') (h : WitA ι r) : WitA ι r' :=
  have k := (flagLaws F Ω l n r).1 r' e
  have k' := (flagLaws F Ω l n r').1 r e.symm'
  ⟨fun v hv u => (k.2.2 v).2 (h.1 v hv ((k'.2.2 v).1 u)), fun π hreg ha =>
    (h.2 π hreg (attC_iso e.symm' ha)).imp fun _ ht v hv => ht v (hv.imp id (k'.2.2 v).2)⟩

/- English proof (translation)
The claim follows from `(aIsoTw P F Ω l ι n r h).2 μ hμ`.
-/
theorem WitA.tw [IsCMField F] (P : Hypotheses₂) {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ) (_hc : Continuous μ) (_ha : IsRegAlgAutomorphicAttached ι r)
    (h : WitA ι r) : WitA ι (Af.tw r μ) := (aIsoTw P F Ω l ι n r h).2 μ hμ

end UpperTheory.V.Z.Win
