import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.RelIndexEqIndexOfMul

namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {G : Type*} [Group G]

/- English proof (translation)
Establish `hN : ∀ k, (F k).Normal` using `fun k => ⟨fun a ha g => by`. Establish `h1` using `(F k).mul_mem (hmono k (hcomm k g a ha)) ha`. Rewrite using `[show g * a * g⁻¹ * a⁻¹ * a = g * a * g⁻¹ by group] at h1⟩` and apply the resulting hypothesis. Establish `hgr : ∀ k, X ⊓ F k ⊔ F (k + 1) = cj g X ⊓ F k ⊔ F (k + 1)`. Introduce `k`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[sup_le_iff]`. Use `⟨?_, le_sup_right⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hy : g * x * g⁻¹ ∈ cj g X ⊓ F k` using `⟨(mem_cj g X _).2 ⟨x, hx.1, rfl⟩, (hN k).conj_mem x hx.2 g⟩`.

Establish `hc` using `hcomm k g x hx.2`. Rewrite using `[show x = (g * x * g⁻¹ * x⁻¹)⁻¹ * (g * x * g⁻¹) by group]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_right ((F (k + 1)).inv_mem hc)) (Subgroup.mem_sup_left hy)`. Rewrite using `[sup_le_iff]`. Use `⟨?_, le_sup_right⟩` and prove the remaining obligations.

Introduce `y hy`. Take `⟨x, hxX, rfl⟩` from `(mem_cj g X y).1 hy.1`. Establish `hxk : x ∈ F k`. Use `(hN k).conj_mem _ hy.2 g⁻¹` as an intermediate fact. Rewrite `this` using `[show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]`. Then use the resulting hypothesis.

Establish `hc` using `hcomm k g x hxk`. Rewrite using `[show g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x by group]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ⟨hxX, hxk⟩)`. Establish `hX : ∀ k (Z : Subgroup G), Z ⊓ F k ⊓ F (k + 1) = Z ⊓ F (k + 1)` using `fun k Z => by`. Rewrite using `[inf_assoc, inf_of_le_right (hmono k)]`.

Establish `main : ∀ j k, k + j = m → (X ⊓ cj g X ⊓ F k).relIndex (X ⊓ F k) = (X ⊓ cj g X ⊓ F k).relIndex (cj g X ⊓ F k)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `k hk`.

Rewrite `hk` using `[Nat.add_zero]`. Substitute `hk` using the available equality. Rewrite using `[hbot]`. Simplify using `only [inf_bot_eq]`. Consider the case `succ j ih`.

Introduce `k hk`. Use `hN (k + 1)` as an intermediate fact. Establish `hle1 : X ⊓ cj g X ⊓ F k ≤ X ⊓ F k` using `inf_le_inf_right _ inf_le_left`. Establish `hle2 : X ⊓ cj g X ⊓ F k ≤ cj g X ⊓ F k` using `inf_le_inf_right _ inf_le_right`. Rewrite using `[relIndex_split (F (k + 1)) _ _ hle1, relIndex_split (F (k + 1)) _ _ hle2, hX k (X ⊓ cj g X), hX k X, hX k (cj g X), ih (k + 1) (by omega), hgr k]`.

Establish `h0` using `main m 0 (by omega)`. Rewrite `h0` using `[htop]`. Simplify using `only [inf_top_eq] at h0`. Rewrite using `[← Subgroup.inf_relIndex_right X (cj g X), ← Subgroup.inf_relIndex_left X (cj g X)]`. Conclude with `h0.symm`.
-/
theorem filt_relIndex (F : ℕ → Subgroup G) (hmono : ∀ k, F (k + 1) ≤ F k)
    (hcomm : ∀ k (g a : G), a ∈ F k → g * a * g⁻¹ * a⁻¹ ∈ F (k + 1)) (m : ℕ)
    (htop : F 0 = ⊤) (hbot : F m = ⊥) (X : Subgroup G) (g : G) :
    X.relIndex (cj g X) = (cj g X).relIndex X := by
  have hN : ∀ k, (F k).Normal := fun k => ⟨fun a ha g => by
    have h1 := (F k).mul_mem (hmono k (hcomm k g a ha)) ha
    rwa [show g * a * g⁻¹ * a⁻¹ * a = g * a * g⁻¹ by group] at h1⟩
  have hgr : ∀ k, X ⊓ F k ⊔ F (k + 1) = cj g X ⊓ F k ⊔ F (k + 1) := by
    intro k
    apply le_antisymm
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      intro x hx
      have hy : g * x * g⁻¹ ∈ cj g X ⊓ F k :=
        ⟨(mem_cj g X _).2 ⟨x, hx.1, rfl⟩, (hN k).conj_mem x hx.2 g⟩
      have hc := hcomm k g x hx.2
      rw [show x = (g * x * g⁻¹ * x⁻¹)⁻¹ * (g * x * g⁻¹) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((F (k + 1)).inv_mem hc))
        (Subgroup.mem_sup_left hy)
    · rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      intro y hy
      obtain ⟨x, hxX, rfl⟩ := (mem_cj g X y).1 hy.1
      have hxk : x ∈ F k := by
        have := (hN k).conj_mem _ hy.2 g⁻¹
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      have hc := hcomm k g x hxk
      rw [show g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ⟨hxX, hxk⟩)
  have hX : ∀ k (Z : Subgroup G), Z ⊓ F k ⊓ F (k + 1) = Z ⊓ F (k + 1) := fun k Z => by
    rw [inf_assoc, inf_of_le_right (hmono k)]
  have main : ∀ j k, k + j = m →
      (X ⊓ cj g X ⊓ F k).relIndex (X ⊓ F k) = (X ⊓ cj g X ⊓ F k).relIndex (cj g X ⊓ F k) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk
      subst hk
      rw [hbot]
      simp only [inf_bot_eq]
    | succ j ih =>
      intro k hk
      have := hN (k + 1)
      have hle1 : X ⊓ cj g X ⊓ F k ≤ X ⊓ F k := inf_le_inf_right _ inf_le_left
      have hle2 : X ⊓ cj g X ⊓ F k ≤ cj g X ⊓ F k := inf_le_inf_right _ inf_le_right
      rw [relIndex_split (F (k + 1)) _ _ hle1, relIndex_split (F (k + 1)) _ _ hle2,
        hX k (X ⊓ cj g X), hX k X, hX k (cj g X), ih (k + 1) (by omega), hgr k]
  have h0 := main m 0 (by omega)
  rw [htop] at h0
  simp only [inf_top_eq] at h0
  rw [← Subgroup.inf_relIndex_right X (cj g X), ← Subgroup.inf_relIndex_left X (cj g X)]
  exact h0.symm

end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
