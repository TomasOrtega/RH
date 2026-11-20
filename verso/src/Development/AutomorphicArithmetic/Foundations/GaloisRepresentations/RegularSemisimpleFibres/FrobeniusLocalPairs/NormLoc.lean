import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp v w hw i1 i2 i3 i4 hmap η hη u`. Take `⟨w0, hw0⟩` from `w`. Take `rfl : below F w0 = v` from `(below_eq_iff w0 v).2 hw0`. Establish `h2` using `ideleNorm_finiteEmbedding (K := F) w0 u`. Establish `h3` using `UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη (IdeleGroup.finiteEmbedding w0 u)`.

Rewrite `h3` using `[h2]`. Establish `hi : i1 = GroundTheory.Global.SemiLocal.algebraCompletion (below F w0) w0`. Apply `Algebra.algebra_ext` to reduce the goal to its premises. Introduce `r`. Conclude with `(hmap r).symm`.

Substitute `hi` using the available equality. Conclude with `h3`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.normLoc :
    UpperTheory.Gal.InertialTypesAlt.L.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw i1 i2 i3 i4 hmap η hη u
  obtain ⟨w0, hw0⟩ := w
  obtain rfl : below F w0 = v := (below_eq_iff w0 v).2 hw0
  have h2 := ideleNorm_finiteEmbedding (K := F) w0 u
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη (IdeleGroup.finiteEmbedding w0 u)
  rw [h2] at h3
  have hi : i1 = GroundTheory.Global.SemiLocal.algebraCompletion (below F w0) w0 := by
    apply Algebra.algebra_ext
    intro r
    exact (hmap r).symm
  subst hi
  exact h3
