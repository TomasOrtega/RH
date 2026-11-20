import Mathlib

namespace GlobalTheory

open Representation

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intertwiner_mem_iSup_range_eq_sum_smul (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj
    rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]

end GlobalTheory
