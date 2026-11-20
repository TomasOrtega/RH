import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Introduce `N k χ G _ hC hχ`. Use `⟨{ toFun := G slash_action_eq' := fun A hA => ?_ holo' := hC.1 zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩` and prove the remaining obligations. Take `⟨A, hA, rfl⟩` from `hA`. Establish `hA0 : A ∈ Gamma0 N` using `Gamma1_in_Gamma0 N hA`. Establish `h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1` using `((Gamma1_mem N A).1 hA).2.1`.

Use `hχ A hA0` as an intermediate fact. Rewrite `this` using `[h11, map_one, one_smul, ModularForm.SL_slash]`. Conclude with `this`. Introduce and unpack `_ ⟨γ, -, rfl⟩`. Conclude with `⟨γ, rfl⟩`.
-/
theorem cuspForm_of_chiInv : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N →
    CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  intro N k χ G _ hC hχ
  refine ⟨{ toFun := G
            slash_action_eq' := fun A hA => ?_
            holo' := hC.1
            zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hA
    have hA0 : A ∈ Gamma0 N := Gamma1_in_Gamma0 N hA
    have h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N A).1 hA).2.1
    have := hχ A hA0
    rw [h11, map_one, one_smul, ModularForm.SL_slash] at this
    exact this
  · rintro _ ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
end GlobalTheory.HeckeFamilyMatrices
