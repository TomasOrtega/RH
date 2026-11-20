import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdempotent

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem asAlgebraHom_centralIdem {Γ V W : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    σ.asAlgebraHom (centralIdem ρ) =
      ∑ g, ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) • σ g := by
  unfold centralIdem
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single _ _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the hypotheses and the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem centralIdemAct : ReciprocityTheory.Ty.Fin.St.CentralIdemAct := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ
  obtain ⟨hVn, hρ'⟩ := hρ
  obtain ⟨hWn, hσ'⟩ := hσ
  haveI := hVn
  haveI := hWn
  haveI hirrρ : ρ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of ρ hρ'
  haveI hirrσ : σ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of σ hσ'
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hW0 : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  obtain ⟨μ, hμ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar σ hσ'
    (fun g => (Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) (by
      intro g k
      have e : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
      have := Representation.char_conj ρ g⁻¹ k
      simp only [Representation.character] at this
      simp only [e, this])
  have hT : σ.asAlgebraHom (centralIdem ρ) = μ • (1 : Module.End ℂ W) := by
    rw [asAlgebraHom_centralIdem]; exact hμ
  have htr : μ * (Module.finrank ℂ W : ℂ) = (Module.finrank ℂ V : ℂ) *
      ((Nat.card Γ : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹) := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum, Finset.mul_sum, Nat.card_eq_fintype_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Representation.character]
    field_simp
  rw [Representation.char_orthonormal σ ρ] at htr
  rw [hT]
  by_cases h : Nonempty (Representation.Equiv ρ σ)
  · rw [if_pos h] at htr ⊢
    obtain ⟨φ⟩ := h
    have hd : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    rw [hd] at htr
    have : μ = 1 := by
      apply mul_right_cancel₀ hW0
      simpa using htr
    rw [this, one_smul]
  · rw [if_neg h] at htr ⊢
    have : μ = 0 := by
      have h0 : μ * (Module.finrank ℂ W : ℂ) = 0 := by simpa using htr
      exact (mul_eq_zero.mp h0).resolve_right hW0
    rw [this, zero_smul]

end GlobalTheory.CompanionTheory.TyFin
