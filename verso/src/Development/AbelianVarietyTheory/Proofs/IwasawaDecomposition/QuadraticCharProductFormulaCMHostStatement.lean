import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHost
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaProduct.eta_product_formula` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FQuadraticCharProductFormulaCMHost.lean&line=411#L411)
-/
theorem _root_.GlobalTheory.T.quadraticChar_product_formula_CM_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : (H.F)ˣ), (∏ᶠ v : HeightOneSpectrum (𝓞 H.F), etaFin (L := H.E) H.F v a) * ∏ w : InfinitePlace H.F, etaInf H.F w a = 1 := by
  first | exact @GlobalTheory.EtaProduct.eta_product_formula | exact GlobalTheory.EtaProduct.eta_product_formula | (intros; apply GlobalTheory.EtaProduct.eta_product_formula <;> assumption)
