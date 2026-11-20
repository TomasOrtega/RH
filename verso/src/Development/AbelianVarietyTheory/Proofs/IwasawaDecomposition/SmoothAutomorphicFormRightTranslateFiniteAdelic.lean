import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.FinTranslate

open GlobalTheory.PointAtPlaceHom

variable {D : D7} {θ : InfF D} {V : HSp D}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem Rder_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ X φ) := by
  funext g
  unfold Rder rTr
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, oneP, comm_of_mem V (atTau_mem V τ _) hk]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem foldr_rTr {α : Type} (k : GA D V) (F : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (h : ∀ a ∈ l, ∀ φ, F a (rTr V k φ) = rTr V k (F a φ)) (φ : GA D V → ℂ) :
    l.foldr F (rTr V k φ) = rTr V k (l.foldr F φ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb), h a List.mem_cons_self]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gelf_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (n : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ n (rTr V k φ) = rTr V k (gelf θ V τ n φ) := by
  unfold gelf
  rw [Finset.sum_congr rfl fun idx _ => foldr_rTr k _ _ (fun a ha ψ => ?_) φ]
  · funext g
    simp only [rTr, Finset.sum_apply]
  · obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    unfold RderC
    rw [Rder_rTr hk, Rder_rTr hk]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAutFunSm_rTr_fin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  intro D θ _ V φ h k hk
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine { left := fun γ hγ g => ?_, level := ?_, cont := h.cont.comp (continuous_mul_right k),
           smooth := fun n τs Xs hX g => ?_, zfin := ?_, growth := ?_ }
  · unfold rTr
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap (MulAut.conj k⁻¹).toMonoidHom, hU.preimage ?_, fun u hu hf g => ?_⟩
    · show Continuous fun u : GA D V => k⁻¹ * u * k⁻¹⁻¹
      fun_prop
    · have hu' : k⁻¹ * u * k⁻¹⁻¹ ∈ U := hu
      have := e _ hu' (mul_mem (mul_mem (inv_mem hk) hf) (inv_mem (inv_mem hk))) (g * k)
      unfold rTr
      rw [← this]
      congr 1
      group
  · have := h.smooth n τs Xs hX (g * k)
    convert this using 2 with t
    unfold rTr
    rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hk]
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    exact atTau_mem V _ _
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (LinearMap.funLeft ℂ ℂ fun g => g * k), inferInstance, ⟨φ, m, rfl⟩, ?_⟩
    rintro τ n _ ⟨f, hf, rfl⟩
    exact ⟨_, s τ n f hf, (gelf_rTr hk τ n f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * k)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_rTr k _ l (fun a _ ψ => Rder_rTr hk _ _ ψ) φ]
    unfold rTr
    rw [mul_assoc, comm_of_mem V hg hk, ← mul_assoc]
    exact hC g hg

end GlobalTheory.Mem.FinTranslate

end
