import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasure
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalSiegelWeilUnramifiedMeasure.lean&line=393#L393)
-/
theorem _root_.GlobalTheory.T.local_siegel_weil_unramified_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : HermR (Fv F v) σ n) (A : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto | exact GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto | (intros; apply GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto <;> assumption)
