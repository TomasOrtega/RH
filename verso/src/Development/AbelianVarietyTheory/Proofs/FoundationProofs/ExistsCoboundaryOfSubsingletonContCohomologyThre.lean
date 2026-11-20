import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ Γ _ _ M _ _ _ _ ρ hs c hc hcoc`. Set `f : (Fin 3 → Γ) → M` to `fun x => c (x 0, x 1, x 2)`. Establish `hf : Continuous f` using `hc.comp (by fun_prop)`. Establish `hd : dn ρ 3 f = 0`. Use function extensionality and compare the values at `g`.

Rewrite using `[dn_apply, Fin.sum_univ_four]`. Establish `e` using `hcoc (g 0) (g 1) (g 2) (g 3)`. Establish `e0 : (f fun i => g i.succ) = c (g 1, g 2, g 3)` using `rfl`. Establish `e1 : f (Fin.contractNth 0 (· * ·) g) = c (g 0 * g 1, g 2, g 3)` using `rfl`. Establish `e2 : f (Fin.contractNth 1 (· * ·) g) = c (g 0, g 1 * g 2, g 3)` using `rfl`.

Establish `e3 : f (Fin.contractNth 2 (· * ·) g) = c (g 0, g 1, g 2 * g 3)` using `rfl`. Establish `e4 : f (Fin.contractNth 3 (· * ·) g) = c (g 0, g 1, g 2)` using `rfl`. Rewrite using `[e0, e1, e2, e3, e4, Pi.zero_apply, ← e]`. Evaluate the numerical expressions using `[pow_succ]`. Normalize the expressions using the abelian group laws.

Rewrite `hs` using `[Submodule.Quotient.subsingleton_iff, eq_top_iff]`. Take `⟨w, hw, hwf⟩ : ∃ w : (Fin 2 → Γ) → M, Continuous w ∧ dn ρ 2 w = f` from `hs (x := ⟨f, hf, hd⟩) trivial`. Use `⟨fun p => w ![p.1, p.2], hw.comp (by fun_prop), fun g h k => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun hwf ![g, h, k]`. Rewrite `e` using `[dn_apply, Fin.sum_univ_three]`.

Establish `e0 : (fun i : Fin 2 => (![g, h, k] : Fin 3 → Γ) i.succ) = ![h, k]`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `e1 : Fin.contractNth 0 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g * h, k]`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `e2 : Fin.contractNth 1 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h * k]`.

Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `e3 : Fin.contractNth 2 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h]`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Establish `e4 : f ![g, h, k] = c (g, h, k)` using `rfl`. Rewrite `e` using `[e0, e1, e2, e3, e4]`.

Rewrite using `[← e]`. Evaluate the numerical expressions using `[pow_succ]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_coboundary_of_subsingleton_Hn_three :
    ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), Subsingleton (Hn ρ 3) → ∀ c : Γ × Γ × Γ → M, Continuous c → (∀ g h k m, ρ g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → M, Continuous u ∧ ∀ g h k, ρ g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k) := by
  intro R _ Γ _ _ M _ _ _ _ ρ hs c hc hcoc
  let f : (Fin 3 → Γ) → M := fun x => c (x 0, x 1, x 2)
  have hf : Continuous f := hc.comp (by fun_prop)
  have hd : dn ρ 3 f = 0 := by
    funext g
    rw [dn_apply, Fin.sum_univ_four]
    have e := hcoc (g 0) (g 1) (g 2) (g 3)
    have e0 : (f fun i => g i.succ) = c (g 1, g 2, g 3) := rfl
    have e1 : f (Fin.contractNth 0 (· * ·) g) = c (g 0 * g 1, g 2, g 3) := rfl
    have e2 : f (Fin.contractNth 1 (· * ·) g) = c (g 0, g 1 * g 2, g 3) := rfl
    have e3 : f (Fin.contractNth 2 (· * ·) g) = c (g 0, g 1, g 2 * g 3) := rfl
    have e4 : f (Fin.contractNth 3 (· * ·) g) = c (g 0, g 1, g 2) := rfl
    rw [e0, e1, e2, e3, e4, Pi.zero_apply, ← e]
    norm_num [pow_succ]
    abel
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff] at hs
  obtain ⟨w, hw, hwf⟩ : ∃ w : (Fin 2 → Γ) → M, Continuous w ∧ dn ρ 2 w = f :=
    hs (x := ⟨f, hf, hd⟩) trivial
  refine ⟨fun p => w ![p.1, p.2], hw.comp (by fun_prop), fun g h k => ?_⟩
  have e := congrFun hwf ![g, h, k]
  rw [dn_apply, Fin.sum_univ_three] at e
  have e0 : (fun i : Fin 2 => (![g, h, k] : Fin 3 → Γ) i.succ) = ![h, k] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g * h, k] := by
    funext i; fin_cases i <;> rfl
  have e2 : Fin.contractNth 1 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h * k] := by
    funext i; fin_cases i <;> rfl
  have e3 : Fin.contractNth 2 (· * ·) (![g, h, k] : Fin 3 → Γ) = ![g, h] := by
    funext i; fin_cases i <;> rfl
  have e4 : f ![g, h, k] = c (g, h, k) := rfl
  rw [e0, e1, e2, e3, e4] at e
  rw [← e]
  norm_num [pow_succ]
  abel

end GlobalTheory
