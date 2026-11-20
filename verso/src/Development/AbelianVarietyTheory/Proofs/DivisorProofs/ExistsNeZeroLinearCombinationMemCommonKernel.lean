import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open GlobalTheory.Nef

namespace GlobalTheory

/- English proof (translation)
Introduce `k F ι _ _ _ n m f hf S N ψ hlt`. Set `T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F)` to `{ toFun := fun c i => ∑ j, c i j • f j map_add' := by`. Introduce `a b`. Use function extensionality and compare the values at `i`. Simplify using `[add_smul, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := by`. Introduce `r a`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.smul_sum, smul_smul] }`. Establish `hT : ∀ c, T c = fun i => ∑ j, c i j • f j` using `fun c => rfl`.

Set `Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k)` to `LinearMap.pi fun v => (ψ v).comp T`. Establish `hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k)`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `only [Module.finrank_fin_fun]`. Rewrite using `[Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]`.

Simplify `hlt` using `[Module.finrank_fin_fun]`. Establish `hk : LinearMap.ker Ψ ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt hlt'`. Take `⟨c, hc, hc0⟩` from `(Submodule.ne_bot_iff _).1 hk`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hc0` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Establish `hi : ∑ j, c i j • f j = 0` using `congrFun h0 i`. Conclude with `Fintype.linearIndependent_iff.1 hf (c i) hi j`. Introduce `v hv`.

Use `congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩` as an intermediate fact. Simplify `this` using `[Ψ, hT]`.
-/
theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
