import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLatticeBasisHermitianSpace.lean&line=260#L260)
-/
theorem _root_.GlobalTheory.T.exists_lattice_basis_hermitian_space : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r), ∃ β : GL (Fin r) (EAf D), LatticeBasisLifts.IsLatBasis V hr β := by
  first | exact @GlobalTheory.LatAdelicBasis.exists_isLatBasis | exact GlobalTheory.LatAdelicBasis.exists_isLatBasis | (intros; apply GlobalTheory.LatAdelicBasis.exists_isLatBasis <;> assumption)
