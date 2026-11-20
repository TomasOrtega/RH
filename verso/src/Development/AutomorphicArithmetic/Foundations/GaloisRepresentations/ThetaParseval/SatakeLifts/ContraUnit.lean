import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqMapBijective

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Replace the chosen expression with an arbitrary variable. Replace the chosen expression with an arbitrary variable. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TP.Loc.contraUnit :
    UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit := by
  intro hci k _ _ _ _ n V _ _ ρ hsm hirr hu
  obtain ⟨B, hherm, hpos, hinv⟩ := hu
  have hnd : ∀ w : V, (∀ v : V, B v w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hpos w hne
    rw [hw w] at h1
    simp at h1
  obtain ⟨w0, hw0⟩ : ∃ w : V, w ≠ 0 := by
    by_contra hne
    push_neg at hne
    haveI : IsSimpleOrder (Subrepresentation ρ) := hirr
    apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    generalize (⊥ : Subrepresentation ρ) = a
    generalize (⊤ : Subrepresentation ρ) = b
    obtain ⟨A, hA⟩ := a
    obtain ⟨A', hA'⟩ := b
    congr 1
    ext x
    rw [hne x]
    simp only [Submodule.zero_mem]
  have hcirr : (contra ρ).IsIrreducible := (hci k n V ρ hsm hirr).1
  have hbij := GlobalTheory.HermDualSelf.sesqMap_bijective ρ hsm B hinv hnd ⟨w0, hw0⟩ hcirr
  have hcomm := GlobalTheory.HermDualSelf.sesqMap_comm ρ hsm B hinv
  set S := GlobalTheory.HermDualSelf.sesqMap ρ hsm B hinv with hS
  let e := LinearEquiv.ofBijective S hbij
  let T : ↥(GlobalTheory.PRep.smoothPart ρ.dual) →ₗ⋆[ℂ] V := e.symm.toLinearMap
  have hST : ∀ f, S (T f) = f := fun f => e.apply_symm_apply f
  have hTS : ∀ w, T (S w) = w := fun w => e.symm_apply_apply w
  have hTg : ∀ g f, T (contra ρ g f) = ρ g (T f) := by
    intro g f
    rw [← hST f, ← hcomm, hTS, hTS]
  refine ⟨⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => B (T f') (T f))
    ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩, ⟨e, fun g x => hcomm g x⟩⟩
  · intro f₁ f₂ f'
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f₁ f₂
    simp [map_add]
  · intro c f f'
    simp [LinearMap.map_smulₛₗ]
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm (T f') (T f)
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (fun h => hf (by rw [← hST f, h, map_zero]))
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [hTg, hTg]
    exact hinv g _ _
