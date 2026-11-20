import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters

namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

/- English proof (translation)
Unfold `wtSub`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

/- English proof (translation)
Proceed by induction on `S using Finset.strongInduction generalizing f with`. Consider the case `H S ih`. Introduce `ν hν`. Distinguish the cases in `h : ∃ μ ∈ S, μ ≠ ν`. Take `⟨μ, hμ, hne⟩` from `h`.

Take `⟨a, ha⟩` from `Function.ne_iff.mp hne`. Set `g : (Ix p q → ℚ) → V` to `fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l`. Establish `hg : ∀ l, g l ∈ wtSub act l` using `fun l => Submodule.smul_mem _ _ (hf l)`. Establish `hsum : ∑ l ∈ S.erase μ, g l = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l`. Rewrite using `[Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[(mem_wtSub_iff act l (f l)).mp (hf l) a]`. Conclude with `sub_smul _ _ _`. Establish `hmem : ∑ l ∈ S.erase μ, g l ∈ N`. Rewrite using `[hsum]`.

Conclude with `N.sub_mem (hN a _ hS) (N.smul_mem _ hS)`. Establish `hgν` using `ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)`. Establish `hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `ha.symm` after adjusting the coercions.

Conclude with `(N.smul_mem_iff hc).mp hgν`. Establish `hone : ∑ l ∈ S, f l = f ν` using `Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h`. Rewrite `hS` using `[hone]`. Then use the resulting hypothesis.
-/
theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by
        rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
