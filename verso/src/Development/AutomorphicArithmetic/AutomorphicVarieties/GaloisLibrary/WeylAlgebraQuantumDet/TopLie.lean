import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve
open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Establish `hc` using `UpperTheory.V.Weyl.curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) (by`. Introduce `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j))`. Use function extensionality and compare the values at `i`.

Establish `h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)`. Establish `h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i`. Use function extensionality and compare the values at `t`.

Rewrite using `[h _ ?_, hfe]`. Both sides reduce to the same expression. Introduce `p q hpq`. Establish `: ¬ (a = p ∧ b = q)`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `absurd hab (not_le.mpr hpq)`. Simplify using `[Matrix.one_apply_ne hpq.ne', Matrix.single_apply, this]`. Rewrite `h1` using `[h2]`. Conclude with `h1.unique (hf.mul_const (v i))`.
-/
private theorem UpperTheory.V.Weyl.top_weight_lie_action (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ)
    (h : Ξ.IsTop ν v) (a b : Fin n) (hab : a ≤ b) (f : ℂ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (hfe : ∀ t : ℂ, ∏ k, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • single a b (1 : ℂ)) k k ^ ν k = f t) :
    Ξ.E a b *ᵥ v = f' • v := by
  have hc := UpperTheory.V.Weyl.curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) (by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j))
  funext i
  have h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0 := by
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)
  have h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i := by
    funext t
    rw [h _ ?_, hfe]
    · rfl
    · intro p q hpq
      have : ¬ (a = p ∧ b = q) := by
        rintro ⟨rfl, rfl⟩
        exact absurd hab (not_le.mpr hpq)
      simp [Matrix.one_apply_ne hpq.ne', Matrix.single_apply, this]
  rw [h2] at h1
  exact h1.unique (hf.mul_const (v i))

/- English proof (translation)
Introduce `n Ξ ν v h`. Use `⟨fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Use `UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _ ?_ ?_` and prove the remaining obligations. Simplify using `using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)`. Introduce `t`.

Rewrite using `[Finset.prod_eq_single a]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Matrix.single_apply, hk.symm]`. Simplify using the standard rewrite rules.

Use `UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) (by` as an intermediate fact. Introduce `t`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: ¬ (a = k ∧ b = k)`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `lt_irrefl _ hab`. Simplify using `[Matrix.single_apply, this])`. Simplify using `using this`.
-/
theorem UpperTheory.V.Weyl.topLie :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), Ξ.IsTop ν v →
      (∀ a, Ξ.E a a *ᵥ v = (ν a : ℂ) • v) ∧ ∀ a b, a < b → Ξ.E a b *ᵥ v = 0 := by
  intro n Ξ ν v h
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _ ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)
    · intro t
      rw [Finset.prod_eq_single a]
      · simp
      · intro k _ hk
        simp [Matrix.single_apply, hk.symm]
      · simp
  · have := UpperTheory.V.Weyl.top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) (by
      intro t
      refine Finset.prod_eq_one fun k _ => ?_
      have : ¬ (a = k ∧ b = k) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [Matrix.single_apply, this])
    simpa using this
