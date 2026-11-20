import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def cellU (F : Type) [Field F] : Set ((Fin 2 → F) × F × F) := {p | p.2.2 ≠ 0 ∧ p.1 1 ≠ 0}

/- English proof (translation)
Establish `h1 : Continuous fun p : (Fin 2 → F) × F × F => p.2.2` using `continuous_snd.snd`. Establish `h2 : Continuous fun p : (Fin 2 → F) × F × F => p.1 1` using `(continuous_apply 1).comp continuous_fst`. Conclude with `(isOpen_compl_singleton.preimage h1).inter (isOpen_compl_singleton.preimage h2)`.
-/
theorem isOpen_cellU : IsOpen (cellU F) := by
  have h1 : Continuous fun p : (Fin 2 → F) × F × F => p.2.2 := continuous_snd.snd
  have h2 : Continuous fun p : (Fin 2 → F) × F × F => p.1 1 := (continuous_apply 1).comp continuous_fst
  exact (isOpen_compl_singleton.preimage h1).inter (isOpen_compl_singleton.preimage h2)

def cellG (p : cellU F) : GL (Fin 2) F :=
  uni2 p.1.2.1 * dg2 (Units.mk0 p.1.2.2 p.2.1) 1 * hr p.1.1

/- English proof (translation)
Establish `he : Topology.IsEmbedding (GJHaar.ch : GL (Fin 2) F → Fin 2 × Fin 2 → F)` using `(Measures.glChart F 2).isOpenEmbedding.isEmbedding`. Rewrite using `[he.continuous_iff]`. Establish `hy : Continuous fun p : cellU F => p.1.2.2` using `continuous_subtype_val.snd.snd`. Establish `hx : Continuous fun p : cellU F => p.1.2.1` using `continuous_subtype_val.snd.fst`. Establish `h0 : Continuous fun p : cellU F => p.1.1 0` using `(continuous_apply 0).comp continuous_subtype_val.fst`.

Establish `h1 : Continuous fun p : cellU F => p.1.1 1` using `(continuous_apply 1).comp continuous_subtype_val.fst`. Establish `hc : (GJHaar.ch ∘ cellG : cellU F → _) = fun p => GJHaar.ent p.1.1 (p.1.2.1 * p.1.1 1) (p.1.2.2 / p.1.1 1 + p.1.2.1 * p.1.1 0)`. Use function extensionality and compare the values at `p`. Conclude with `GJHaar.ch_g _ _ p.2.2`. Rewrite using `[hc]`.

Use `continuous_pi fun ij => ?_` and prove the remaining obligations. Take `⟨i, j⟩` from `ij`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `(hy.div h1 fun p => p.2.2).add (hx.mul h0)`. Conclude with `hx.mul h1`.

Conclude with `h0`. Conclude with `h1`.
-/
theorem continuous_cellG : Continuous (cellG : cellU F → GL (Fin 2) F) := by
  have he : Topology.IsEmbedding (GJHaar.ch : GL (Fin 2) F → Fin 2 × Fin 2 → F) :=
    (Measures.glChart F 2).isOpenEmbedding.isEmbedding
  rw [he.continuous_iff]
  have hy : Continuous fun p : cellU F => p.1.2.2 := continuous_subtype_val.snd.snd
  have hx : Continuous fun p : cellU F => p.1.2.1 := continuous_subtype_val.snd.fst
  have h0 : Continuous fun p : cellU F => p.1.1 0 := (continuous_apply 0).comp continuous_subtype_val.fst
  have h1 : Continuous fun p : cellU F => p.1.1 1 := (continuous_apply 1).comp continuous_subtype_val.fst
  have hc : (GJHaar.ch ∘ cellG : cellU F → _) = fun p =>
      GJHaar.ent p.1.1 (p.1.2.1 * p.1.1 1) (p.1.2.2 / p.1.1 1 + p.1.2.1 * p.1.1 0) := by
    funext p
    exact GJHaar.ch_g _ _ p.2.2
  rw [hc]
  refine continuous_pi fun ij => ?_
  obtain ⟨i, j⟩ := ij
  fin_cases i <;> fin_cases j
  · exact (hy.div h1 fun p => p.2.2).add (hx.mul h0)
  · exact hx.mul h1
  · exact h0
  · exact h1

end GlobalTheory.CompanionTheory.GJTwo
