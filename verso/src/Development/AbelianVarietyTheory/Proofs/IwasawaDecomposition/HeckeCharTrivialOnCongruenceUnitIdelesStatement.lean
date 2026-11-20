import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdeles
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelChars.LevTriv.levSub_triv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckeCharTrivialOnCongruenceUnitIdeles.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  first | exact @GlobalTheory.LevelChars.LevTriv.levSub_triv | exact GlobalTheory.LevelChars.LevTriv.levSub_triv | (intros; apply GlobalTheory.LevelChars.LevTriv.levSub_triv <;> assumption)
