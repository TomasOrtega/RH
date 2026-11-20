import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEq
import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PatchAtSelf
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSameAtOfLocalizationEq.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.sameAt_of_localization_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  first | exact @GlobalTheory.sameAt_of_localized_eq | exact GlobalTheory.sameAt_of_localized_eq | (intros; apply GlobalTheory.sameAt_of_localized_eq <;> assumption)
