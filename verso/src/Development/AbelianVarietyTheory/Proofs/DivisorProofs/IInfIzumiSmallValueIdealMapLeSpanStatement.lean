import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfIzumiSmallValueIdealMapLeSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIInfIzumiSmallValueIdealMapLeSpan.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  first | exact @GlobalTheory.Izumi.iInf_map_smallIdeal_le_span | exact GlobalTheory.Izumi.iInf_map_smallIdeal_le_span | (intros; apply GlobalTheory.Izumi.iInf_map_smallIdeal_le_span <;> assumption)
