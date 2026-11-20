import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeShortExact
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HodgeSeqSheaf.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeRhamHodgeShortExact.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.de_rham_hodge_short_exact : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
    ∀ H : T.Modules, GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H →
      ∃ S : ShortComplex T.Modules, S.ShortExact ∧ Nonempty (S.X₂ ≅ H) ∧
        Nonempty (S.X₁ ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) ∧ Nonempty (S.X₃ ≅ GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  first | exact @GlobalTheory.HodgeSeqSheaf.main | exact GlobalTheory.HodgeSeqSheaf.main | (intros; apply GlobalTheory.HodgeSeqSheaf.main <;> assumption)
