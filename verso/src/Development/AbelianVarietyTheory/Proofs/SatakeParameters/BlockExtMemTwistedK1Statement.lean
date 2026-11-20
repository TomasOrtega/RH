import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockExtMemTwistedK1
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.ChainTwTopQ
import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TopStep.ext_mem_twisted_k1_level` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FBlockExtMemTwistedK1.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.block_ext_mem_twisted_k1 : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ {N n : ℕ} (hN : N = n + 1) (r b c : ℕ), n = r + b → ∀ j : GLint E n P, redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b → extI hN P j ∈ twK1H P N r c := by
  first | exact @GlobalTheory.TopStep.ext_mem_twisted_k1_level | exact GlobalTheory.TopStep.ext_mem_twisted_k1_level | (intros; apply GlobalTheory.TopStep.ext_mem_twisted_k1_level <;> assumption)
