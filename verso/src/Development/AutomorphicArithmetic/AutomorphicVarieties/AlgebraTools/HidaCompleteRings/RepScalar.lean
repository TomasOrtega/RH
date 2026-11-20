import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepEigSum

open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repScalar :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type} [AddCommGroup N] [Module k N] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (σ : Representation k G N), IsSmooth σ → ∀ (Y : Submodule k V), Y ≤ copies ρ Y σ → ∀ (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → (Y ⊓ eig ρ K χ ≠ ⊥ → eig σ K χ ≠ ⊥) ∧ ∀ (A : Module.End k V) (A' : Module.End k N) (a : k), (∀ f : Into ρ Y σ, ∀ n ∈ eig σ K χ, A (f.1 n) = f.1 (A' n)) → (∀ n ∈ eig σ K χ, A' n = a • n) → ∀ v ∈ Y ⊓ eig ρ K χ, A v = a • v := by
  intro k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y hY K χ hK hχ
  have key : Y ⊓ eig ρ K χ ≤ ⨆ f : Into ρ Y σ, Submodule.map (f : N →ₗ[k] V) (eig σ K χ) := by
    rw [← repEigSum ρ σ hσ Y K χ hK hχ]
    exact inf_le_inf_right _ hY
  refine ⟨fun hne hσ0 => hne ?_, ?_⟩
  · apply le_bot_iff.mp
    refine key.trans ?_
    simp [hσ0]
  · intro A A' a hA hA' v hv
    refine Submodule.iSup_induction (fun f : Into ρ Y σ => Submodule.map (f : N →ₗ[k] V) (eig σ K χ))
      (motive := fun x => A x = a • x) (key hv) ?_ ?_ ?_
    · intro f w hw
      obtain ⟨n, hn, rfl⟩ := hw
      have h1 := hA f n hn
      rw [hA' n hn, map_smul] at h1
      exact h1
    · simp
    · intro x y hx hy
      rw [map_add, hx, hy, smul_add]
