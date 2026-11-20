import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

/- English proof (translation)
Establish `h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0}`. Use extensionality with `x`. Simplify using `only [Set.mem_iInter, Set.mem_ofPred_eq]`. Conclude with `Iff.rfl`. Rewrite using `[h]`.

Use `isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const`.
-/
theorem isClosed_Kset {p q : ℕ} (T : GrpData p q) : IsClosed T.Kset := by
  have h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const

/- English proof (translation)
Introduce `p q T`. Establish `hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1)`. Use `(Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)` and prove the remaining obligations. Introduce `z hz`. Establish `: z ≠ 0` using `by rintro rfl; simp at hz`.

Conclude with `⟨Units.mk0 z this, rfl⟩`. Establish `hc` using `Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1}) (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)`. Use `((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩` and prove the remaining obligations. Simplify using `using GlobalTheory.RealPar.Cover.norm_sq x`.
-/
theorem isCompact_Kset : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  intro p q T
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset
    (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

end GlobalTheory.PolarU
