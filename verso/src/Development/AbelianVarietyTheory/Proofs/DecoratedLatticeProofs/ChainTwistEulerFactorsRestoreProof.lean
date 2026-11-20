import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreQuotientLValuesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

/- English proof (translation)
Introduce `D _ c w hw k hk s s' hs hs' _ _`. Take `⟨hr, -, hfl⟩` from `hs`. Take `⟨hr', -, hfl'⟩` from `hs'`. Establish `h1 : s.V.rank = D.R.rankY k` using `hfl.rank`. Establish `h2 : s'.V.rank = D.R.rankY k + D.R.t`.

Establish `h : s'.V.rank = D.R.rankY (k + 1)` using `hfl'.rank`. Rewrite using `[h]`. Simplify using `only [Formalism.BasicNotions.Ranks.rankY]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : D.R.rankY k + D.R.t = D.R.r + (k + 1) * D.R.t`.

Simplify using `only [Formalism.BasicNotions.Ranks.rankY]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨hL, hL₀⟩` from `GlobalTheory.T.twistEulerFactors_restore_quotientLValues D c w hw k hk`. Take `⟨hd0, hd⟩` from `GlobalTheory.T.twistEulerFactors_restore_normalizingFactor D c w hw (D.R.rankY k)`. Use `⟨hL, hL₀, ?_, ?_⟩` and prove the remaining obligations.

Unfold `dS`. Rewrite using `[h1, h2]`. Conclude with `hd0`. Unfold `dS`. Rewrite using `[h1, h2, hd, h3]`.
-/
theorem restore_holds : ∀ D : D7, Restore D := by
  intro D _ c w hw k hk s s' hs hs' _ _
  obtain ⟨hr, -, hfl⟩ := hs
  obtain ⟨hr', -, hfl'⟩ := hs'
  have h1 : s.V.rank = D.R.rankY k := hfl.rank
  have h2 : s'.V.rank = D.R.rankY k + D.R.t := by
    have h : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h]; simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  have h3 : D.R.rankY k + D.R.t = D.R.r + (k + 1) * D.R.t := by
    simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  obtain ⟨hL, hL₀⟩ := GlobalTheory.T.twistEulerFactors_restore_quotientLValues D c w hw k hk
  obtain ⟨hd0, hd⟩ := GlobalTheory.T.twistEulerFactors_restore_normalizingFactor D c w hw (D.R.rankY k)
  refine ⟨hL, hL₀, ?_, ?_⟩
  · unfold dS; rw [h1, h2]; exact hd0
  · unfold dS; rw [h1, h2, hd, h3]

end GlobalTheory.ChainTw
