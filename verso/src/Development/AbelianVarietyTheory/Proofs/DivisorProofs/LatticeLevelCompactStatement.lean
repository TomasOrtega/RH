import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThKLevelCpt.isCompact_latLevel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeLevelCompact.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.lattice_level_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.L.IsLattice E → IsCompact (GlobalTheory.ThKLevel.latLevel σ W : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) := by
  first | exact @GlobalTheory.ThKLevelCpt.isCompact_latLevel | exact GlobalTheory.ThKLevelCpt.isCompact_latLevel | (intros; apply GlobalTheory.ThKLevelCpt.isCompact_latLevel <;> assumption)
