import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem orthogonal_kstable_compl : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  intro R S W _ _ _ actW B hB U hU
  obtain ⟨_, hpos, hadj⟩ := hB
  constructor
  · intro X hX x hx
    refine GlobalTheory.TensorHW.kc_ind actW (U.orthogonalBilin B) x (fun a b hab => ?_) hX
    rw [Submodule.mem_orthogonalBilin_iff] at hx ⊢
    intro n hn
    have hba : sameBlock b a := by
      cases a <;> cases b <;> simp_all [sameBlock]
    have h := hadj b a hba n x
    show B n (actW (Eab a b) x) = 0
    rw [← h]
    exact hx _ (hU _ (GlobalTheory.TensorHW.isKC_Eab hba) n hn)
  · have hinf : U ⊓ U.orthogonalBilin B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxo⟩ := Submodule.mem_inf.mp hx
      rw [Submodule.mem_orthogonalBilin_iff] at hxo
      have h0 : B x x = 0 := hxo x hxU
      rw [Submodule.mem_bot]
      by_contra hne
      have h := hpos x hne
      rw [h0] at h
      simp at h
    let b := Module.finBasis ℂ U
    let ψ : W →ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ) := LinearMap.pi (fun i => B (b i : W))
    have hker : LinearMap.ker ψ ≤ U.orthogonalBilin B := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_orthogonalBilin_iff]
      intro n hn
      have hf : (B.flip x).comp U.subtype = 0 := by
        refine b.ext (fun i => ?_)
        have h := congrFun hx i
        simpa [ψ] using h
      have h := LinearMap.congr_fun hf ⟨n, hn⟩
      simpa using h
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : Module.finrank ℂ (LinearMap.range ψ) ≤ Module.finrank ℂ U := by
      have h := Submodule.finrank_le (LinearMap.range ψ)
      simpa using h
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (U.orthogonalBilin B)
    rw [hinf, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    omega

end GlobalTheory.SteepMult
