import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

/- English proof (translation)
Introduce `H _ _ _ _ _ _ N M π σ hπ hσ hirr hcomm Hm hHm`. Establish `key : ∀ T₁ ∈ Hm, T₁ ≠ 0 → ∀ T₂ ∈ Hm, ∃ c : ℂ, c • T₁ = T₂`. Introduce `T₁ h₁ hne T₂ h₂`. Rewrite `h₁`, `h₂` using `[hHm]`. Take `⟨X, hX⟩` from `hI H N M π σ hirr T₁ h₁ hne`.

Take `⟨S, hSeq, hST⟩` from `hA H N M π σ hπ hσ T₁ X h₁ hX`. Take `⟨c, hc⟩` from `hS H M σ hirr (S * T₂) (fun g => by`. Rewrite using `[← Matrix.mul_assoc, hSeq g, Matrix.mul_assoc, h₂ g, Matrix.mul_assoc])`. Use `⟨c, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`.

Use `set T := T₂ - c • T₁ with hT`. Establish `hT0 : T ≠ 0` using `sub_ne_zero.mpr (Ne.symm hne')`. Establish `hTeq : ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T = T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ)` using `fun g => by`. Rewrite using `[hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h₁ g, h₂ g]`. Establish `hST0 : S * T = 0`.

Rewrite using `[hT, Matrix.mul_sub, Matrix.mul_smul, hST, hc, sub_self]`. Take `⟨X', hX'⟩` from `hI H N M π σ hirr T hTeq hT0`. Take `⟨S', hS'eq, hS'T⟩` from `hA H N M π σ hπ hσ T X' hTeq hX'`. Establish `hP : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T₁ * S') = (T₁ * S') * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `fun g => by`. Rewrite using `[← Matrix.mul_assoc, h₁ g, Matrix.mul_assoc, hS'eq g, Matrix.mul_assoc]`.

Establish `hQ : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T * S) = (T * S) * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)` using `fun g => by`. Rewrite using `[← Matrix.mul_assoc, hTeq g, Matrix.mul_assoc, hSeq g, Matrix.mul_assoc]`. Establish `hPQ` using `hcomm _ _ hP hQ`. Establish `e1 : T₁ * S' * (T * S) = T₁ * S`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc S', hS'T, Matrix.one_mul]`.

Establish `e2 : T * S * (T₁ * S') = T * S'`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc S, hST, Matrix.one_mul]`. Establish `e3 : T₁ * S = T * S'` using `by rw [← e1, ← e2, hPQ]`. Establish `e4 : S = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hST` using `[e4, Matrix.zero_mul]`. Establish `hM : M = 0`. Assume the negation of the conclusion as `hM`. Establish `h` using `congrFun (congrFun hST ⟨0, Nat.pos_of_ne_zero hM⟩) ⟨0, Nat.pos_of_ne_zero hM⟩`. Simplify using `at h`.

Substitute `hM` using the available equality. Conclude with `hT0 (Matrix.ext fun _ j => j.elim0)`. Distinguish the cases in `h0 : ∃ T₁ ∈ Hm, T₁ ≠ 0`. Take `⟨T₁, h₁, hne⟩` from `h0`. Apply `finrank_le_one (⟨T₁, h₁⟩ : Hm)` to reduce the goal to its premises.

Introduce `w`. Take `⟨c, hc⟩` from `key T₁ h₁ hne w.1 w.2`. Conclude with `⟨c, Subtype.ext hc⟩`. Use `push Not at h0`. Establish `hb : Hm = ⊥` using `(Submodule.eq_bot_iff _).mpr h0`.

Substitute `hb` using the available equality. Simplify using the standard rewrite rules.
-/
theorem commMult_of (hS : SchurStep) (hI : InjStep) (hA : AvStep) : PI.UMultOne.CommutantMult := by
  intro H _ _ _ _ _ _ N M π σ hπ hσ hirr hcomm Hm hHm
  have key : ∀ T₁ ∈ Hm, T₁ ≠ 0 → ∀ T₂ ∈ Hm, ∃ c : ℂ, c • T₁ = T₂ := by
    intro T₁ h₁ hne T₂ h₂
    rw [hHm] at h₁ h₂
    obtain ⟨X, hX⟩ := hI H N M π σ hirr T₁ h₁ hne
    obtain ⟨S, hSeq, hST⟩ := hA H N M π σ hπ hσ T₁ X h₁ hX
    obtain ⟨c, hc⟩ := hS H M σ hirr (S * T₂) (fun g => by
      rw [← Matrix.mul_assoc, hSeq g, Matrix.mul_assoc, h₂ g, Matrix.mul_assoc])
    refine ⟨c, ?_⟩
    by_contra hne'
    set T := T₂ - c • T₁ with hT
    have hT0 : T ≠ 0 := sub_ne_zero.mpr (Ne.symm hne')
    have hTeq : ∀ g, ((π g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * T =
        T * ((σ g : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) := fun g => by
      rw [hT, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h₁ g, h₂ g]
    have hST0 : S * T = 0 := by
      rw [hT, Matrix.mul_sub, Matrix.mul_smul, hST, hc, sub_self]
    obtain ⟨X', hX'⟩ := hI H N M π σ hirr T hTeq hT0
    obtain ⟨S', hS'eq, hS'T⟩ := hA H N M π σ hπ hσ T X' hTeq hX'
    have hP : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T₁ * S') =
        (T₁ * S') * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, h₁ g, Matrix.mul_assoc, hS'eq g, Matrix.mul_assoc]
    have hQ : ∀ h, ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (T * S) =
        (T * S) * ((π h : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun g => by
      rw [← Matrix.mul_assoc, hTeq g, Matrix.mul_assoc, hSeq g, Matrix.mul_assoc]
    have hPQ := hcomm _ _ hP hQ
    have e1 : T₁ * S' * (T * S) = T₁ * S := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S', hS'T, Matrix.one_mul]
    have e2 : T * S * (T₁ * S') = T * S' := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hST, Matrix.one_mul]
    have e3 : T₁ * S = T * S' := by rw [← e1, ← e2, hPQ]
    have e4 : S = 0 := by
      calc S = S * T₁ * S := by rw [hST, Matrix.one_mul]
        _ = S * T * S' := by rw [Matrix.mul_assoc, e3, ← Matrix.mul_assoc]
        _ = 0 := by rw [hST0, Matrix.zero_mul]
    rw [e4, Matrix.zero_mul] at hST
    have hM : M = 0 := by
      by_contra hM
      have h := congrFun (congrFun hST ⟨0, Nat.pos_of_ne_zero hM⟩) ⟨0, Nat.pos_of_ne_zero hM⟩
      simp at h
    subst hM
    exact hT0 (Matrix.ext fun _ j => j.elim0)
  by_cases h0 : ∃ T₁ ∈ Hm, T₁ ≠ 0
  · obtain ⟨T₁, h₁, hne⟩ := h0
    apply finrank_le_one (⟨T₁, h₁⟩ : Hm)
    intro w
    obtain ⟨c, hc⟩ := key T₁ h₁ hne w.1 w.2
    exact ⟨c, Subtype.ext hc⟩
  · push Not at h0
    have hb : Hm = ⊥ := (Submodule.eq_bot_iff _).mpr h0
    subst hb
    simp

end PI.UnitaryGroupMassFormula.CommMult
