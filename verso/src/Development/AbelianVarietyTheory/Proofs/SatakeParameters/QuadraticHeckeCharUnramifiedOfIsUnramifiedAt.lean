import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.QuadCharUnr

/- English proof (translation)
Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E` using `E) (w.under (𝓞 (maximalRealSubfield E))) := by`. Distinguish the cases in `hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))`. Conclude with `GlobalTheory.LFun.isUnram_of_isSplit h2 hs`. Use `GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_` and prove the remaining obligations.

Take `rfl` from `GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl`. Use `haveI := u.isPrime`. Conclude with `Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw`. Introduce `x hx`. Establish `hn` using `GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx`.

Express the relevant statement in the definitionally equal form `Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1`. Rewrite using `[GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]`.
-/
theorem quadChar_unrAt_of_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      haveI := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

end GlobalTheory.QuadCharUnr
