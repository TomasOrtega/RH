import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CS (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (CS ψ) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem CS_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c d : ℕ} (hc : c ∈ CS ψ) (hcd : c ≤ d) : d ∈ CS ψ := by
  intro u hu
  exact hc u (Ideal.pow_le_pow_right hcd hu)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem CS_inv (ψ : 𝒪[k]ˣ →* ℂˣ) : CS ψ⁻¹ = CS ψ := by
  ext c
  simp only [CS, Set.mem_setOf_eq, MonoidHom.inv_apply, inv_eq_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cond_one : cond (1 : 𝒪[k]ˣ →* ℂˣ) = 0 := by
  rw [cond_eq]
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem res_div_swap {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) :
    res (μ b / μ a) = (res (μ a / μ b))⁻¹ := by
  ext u
  simp [res, MonoidHom.div_apply, MonoidHom.inv_apply, inv_div]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem res_div_mul {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s) (u : 𝒪[k]ˣ) :
    res (μ a / μ c) u = res (μ a / μ b) u * res (μ b / μ c) u := by
  simp [res, MonoidHom.div_apply, div_mul_div_cancel₀]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cc_self {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a : Fin s) : cc μ a a = 0 := by
  unfold cc
  rw [div_self']
  exact cond_one

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem cc_comm {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : cc μ a b = cc μ b a := by
  unfold cc
  rw [res_div_swap μ a b, cond_eq, cond_eq, CS_inv]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cc_ultra {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s)
    (hab : (CS (res (μ a / μ b))).Nonempty) (hbc : (CS (res (μ b / μ c))).Nonempty) :
    cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  have h1 : cc μ a b ∈ CS (res (μ a / μ b)) := Nat.sInf_mem hab
  have h2 : cc μ b c ∈ CS (res (μ b / μ c)) := Nat.sInf_mem hbc
  have h3 : max (cc μ a b) (cc μ b c) ∈ CS (res (μ a / μ c)) := by
    intro u hu
    rw [res_div_mul μ a b c u,
      CS_mono _ h1 (le_max_left _ _) u hu, CS_mono _ h2 (le_max_right _ _) u hu, one_mul]
  exact Nat.sInf_le h3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem step_ccBasic_of_cond :
    ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
      (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c →
        res (μ a / μ b) u = 1) →
      ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  intro s μ hμ a b c
  refine ⟨cc_self μ a, cc_comm μ a b, cc_ultra μ a b c ?_ ?_⟩
  · obtain ⟨c0, h⟩ := hμ a b
    exact ⟨c0, h⟩
  · obtain ⟨c0, h⟩ := hμ b c
    exact ⟨c0, h⟩

end CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem step_ccBasic : CompactConductorBasicProp (k := k) :=
  CharacterConductor.step_ccBasic_of_cond

end Grp

end UpperTheory.TNZ
