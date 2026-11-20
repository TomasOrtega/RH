import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct Topology

namespace GlobalTheory.IntDense

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_of_isClosed (F : Type) [Field F] [NumberField F] {C : Set (FiniteAdeleRing (𝓞 F) F)}
    (hC : IsClosed C) (h : ∀ a : 𝓞 F, algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ C)
    (α : FiniteAdeleRing (𝓞 F) F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) : α ∈ C := by
  by_contra hn
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F => α - y := continuous_const.sub continuous_id
  have hU : (fun y : FiniteAdeleRing (𝓞 F) F => α - y) ⁻¹' Cᶜ ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    (hC.isOpen_compl.preimage hc).mem_nhds (by simpa using hn)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hU
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).2 α hα
  refine hNU β hβ ?_
  change α - N • β ∈ C
  rw [e, add_sub_cancel_right]
  exact h a

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem addChar_eq_one_of_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : F, (∀ a : 𝓞 F, ψ (pairA F 0 (algebraMap F (Af F) ((a : F) * x))) = 1) → ∀ α ∈ intAf F, ψ (pairA F 0 (α * algebraMap F (Af F) x)) = 1 := by
  intro F _ _ ψ hψ x h α hα
  have hp : Continuous fun y : Af F => pairA F 0 (y * algebraMap F (Af F) x) :=
    Continuous.prodMk continuous_const (continuous_id.mul continuous_const)
  refine mem_of_isClosed F (C := {y | ψ (pairA F 0 (y * algebraMap F (Af F) x)) = 1})
    (isClosed_eq (hψ.comp hp) continuous_const) (fun a => ?_) α hα
  have := h a
  rwa [map_mul] at this

end GlobalTheory.IntDense
