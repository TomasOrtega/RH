import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open Classical in

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mult_equiv_update {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h h' =>
    funext z
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext z
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem multT_cont_left_equiv :
    ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ), AllPlus M → (∀ τ, M.sm τ = ⊤) → Function.Injective (inclT M) → IsTensAct M π → ∀ L ∈ MultT θ M J χ, ∀ x, Continuous (L x) ∧ (∀ γ ∈ GQ V, ∀ h, L x (γ * h) = L x h) ∧ ∀ τ u, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x) := by
  classical
  intro D θ V S M π J χ hp hsm hinj hπ L hL x
  rw [mem_multT] at hL
  have hv : ∀ v, L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm L v := fun v => rfl
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    obtain ⟨a, b, -⟩ := mult_value_left_cont_level θ M J χ _ hL v
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_smul, hv]; exact b.const_smul r
    · rw [map_smul, hv]; simp only [Pi.smul_apply, a γ hγ h]
    · let w : M.sm τ := ⟨M.rep τ (unfr M τ u) (v τ), Submodule.eq_top_iff'.1 (hsm τ) _⟩
      have e : π τ u (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ w) := by
        apply hinj
        rw [hπ]
        unfold inclT actT
        simp only [PiTensorProduct.map_tprod]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst hρ
          simp [w]
        · simp [Function.update_of_ne hρ]
      rw [map_smul, map_smul, map_smul, e, hv, hv,
        mult_equiv_update θ M J χ _ hL τ _ (hp.unfr_mem τ u) v w rfl]
      rfl
  | add x y hx hy =>
    obtain ⟨a, b, c⟩ := hx
    obtain ⟨a', b', c'⟩ := hy
    refine ⟨?_, fun γ hγ h => ?_, fun τ u => ?_⟩
    · rw [map_add]; exact a.add a'
    · simp only [map_add, Pi.add_apply, b γ hγ h, b' γ hγ h]
    · rw [map_add, map_add, map_add, c, c']; rfl

end GlobalTheory
