import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsSelfDualLatticeCompletionMaxOrder.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.exists_selfDualLattice_completion_maxOrder : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), IsHermND σ J → Submodule.IsLattice E L → (∀ y : Fin n → E, y ∈ L ↔ ∀ x ∈ L, hE σ J x y ∈ (algebraMap (𝓞 E) E).range) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ Lv : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin n → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v Lv ∧ ∀ y, y ∈ Lv ↔ y ∈ GlobalTheory.AdelicU.latLoc F L v := by
  first | exact @GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | exact GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice | (intros; apply GlobalTheory.CompletedSelfDual.exists_isSelfDualLattice <;> assumption)
