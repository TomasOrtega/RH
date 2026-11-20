import Mathlib
open scoped Matrix
open Polynomial

namespace GlobalTheory.CyclicVector

/- English proof (translation)
Take `⟨x, hx⟩` from `Module.exists_ker_toSpanSingleton_eq_annihilator K[X] (Module.AEval' (Matrix.toLin' g))`. Use `set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv`. Use `⟨v, ?_⟩` and prove the remaining obligations. Rewrite `hg`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `c hc`.

Set `q : K[X]` to `∑ j : Fin r, monomial (j : ℕ) (c j)`. Establish `haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ)`. Simplify using `[q, map_sum, aeval_monomial, Algebra.smul_def]`. Establish `ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p)` using `fun p => (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)`. Establish `hqv : aeval g q *ᵥ v = 0`.

Rewrite using `[haq, Matrix.sum_mulVec]`. Establish `hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v)` using `fun j => by`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Simplify `hc` using `[hs]`.

Establish `hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g))`. Rewrite using `[← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Apply `(Module.AEval'.of (Matrix.toLin' g)).symm.injective` to reduce the goal to its premises. Rewrite using `[Module.AEval.of_symm_smul, map_zero, ha]`. Conclude with `hqv`.

Establish `hq : aeval g q = 0`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[map_zero, ← ha]`. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Use `Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)` as an intermediate fact.

Establish `h2` using `congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this`. Rewrite `h2` using `[Module.AEval.of_symm_smul, map_zero]`. Simplify using `using h2`. Conclude with `hg c (haq ▸ hq)`.
-/
theorem exists_linearIndependent_iterates_of_linearIndependent_pow {K : Type} [Field K] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) K)
    (hg : LinearIndependent K (fun i : Fin r => g ^ (i : ℕ))) :
    ∃ v : Fin r → K, LinearIndependent K (fun i : Fin r => (g ^ (i : ℕ)) *ᵥ v) := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  refine ⟨v, ?_⟩
  rw [Fintype.linearIndependent_iff] at hg ⊢
  intro c hc
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (c j)
  have haq : aeval g q = ∑ j : Fin r, c j • g ^ (j : ℕ) := by
    simp [q, map_sum, aeval_monomial, Algebra.smul_def]
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [haq, Matrix.sum_mulVec]
    have hs : ∀ j : Fin r, (c j • g ^ (j : ℕ)) *ᵥ v = c j • (g ^ (j : ℕ) *ᵥ v) := fun j => by
      ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simpa [hs] using hc
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  exact hg c (haq ▸ hq)

end GlobalTheory.CyclicVector
