import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ R _ _ _ τ hτ hrk n ι _ u hcard hu g`. Establish `hq : ∀ c : ℚ, τ (algebraMap ℚ E c) = algebraMap ℝ R (algebraMap ℚ ℝ c)`. Introduce `c`. Establish `: τ.comp (algebraMap ℚ E) = (algebraMap ℝ R).comp (algebraMap ℚ ℝ)` using `Subsingleton.elim _ _`. Conclude with `congrArg (fun f : ℚ →+* R => f c) this`.

Use `set V : Submodule ℝ (Fin n → R) := Submodule.span ℝ (Set.range fun k => (fun i => τ (u k i))) with hV`. Establish `h1 : ∀ x : Fin n → E, (fun i => τ (x i)) ∈ V`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℚ (Set.range u)` using `by rw [hu]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨k, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Consider the case `zero`. Establish `: (fun i => τ ((0 : Fin n → E) i)) = 0` using `by ext i; simp`.

Rewrite using `[this]`. Conclude with `V.zero_mem`. Consider the case `add x y _ _ hx hy`. Establish `: (fun i => τ ((x + y) i)) = (fun i => τ (x i)) + (fun i => τ (y i))`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `V.add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `: (fun i => τ ((c • x) i)) = (algebraMap ℚ ℝ c) • (fun i => τ (x i))`.

Use extensionality with `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hq]`. Rewrite using `[this]`. Conclude with `V.smul_mem _ hx`. Establish `h2 : ∀ (i : Fin n) (r : R), Pi.single i r ∈ V`.

Introduce `i r`. Establish `hle : Submodule.span ℝ (Set.range τ) ≤ V.comap (LinearMap.single ℝ (fun _ : Fin n => R) i)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨e, rfl⟩`. Use `h1 (Pi.single i e)` as an intermediate fact.

Establish `h' : (fun j => τ ((Pi.single i e : Fin n → E) j)) = Pi.single i (τ e)`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hj]`. Rewrite `this` using `[h']`. Conclude with `this`. Establish `hr : r ∈ Submodule.span ℝ (Set.range τ)` using `by rw [hτ]; trivial`. Conclude with `hle hr`.

Establish `h3 : ∀ y : Fin n → R, y ∈ V`. Introduce `y`. Rewrite using `[← Finset.univ_sum_single y]`. Conclude with `V.sum_mem fun i _ => h2 i _`. Set `φ : (Fin n → R) →ₗ[ℝ] (Fin n → R)` to `{ toFun := fun v => v ᵥ* g.1 map_add' := fun v w => Matrix.add_vecMul _ _ _ map_smul' := fun c v => Matrix.smul_vecMul _ _ _ }`.

Apply `linearIndependent_of_top_le_span_of_card_eq_finrank` to reduce the goal to its premises. Introduce `y _`. Establish `hy : y = φ (y ᵥ* (g⁻¹).1)`. Simplify using `[φ, Matrix.vecMul_vecMul]`. Establish `hm : φ (y ᵥ* (g⁻¹).1) ∈ V.map φ` using `Submodule.mem_map_of_mem (h3 _)`.

Rewrite `hm` using `[hV, Submodule.map_span, ← Set.range_comp]`. Rewrite using `[hy]`. Conclude with `hm`. Rewrite using `[hcard, Module.finrank_pi_fintype, ← hrk]`. Simplify using `[mul_comm]`.
-/
theorem linearIndependent_vecMul_of_span_rat :
    ∀ (E : Type) [Field E] [NumberField E] (R : Type) [CommRing R] [Algebra ℝ R] [FiniteDimensional ℝ R] (τ : E →+* R), Submodule.span ℝ (Set.range τ) = ⊤ → Module.finrank ℝ R = Module.finrank ℚ E → ∀ (n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin n → E), Fintype.card ι = Module.finrank ℚ E * n → Submodule.span ℚ (Set.range u) = ⊤ → ∀ g : GL (Fin n) R, LinearIndependent ℝ fun k => (fun i => τ (u k i)) ᵥ* g.1 := by
  intro E _ _ R _ _ _ τ hτ hrk n ι _ u hcard hu g
  classical
  have hq : ∀ c : ℚ, τ (algebraMap ℚ E c) = algebraMap ℝ R (algebraMap ℚ ℝ c) := by
    intro c
    have : τ.comp (algebraMap ℚ E) = (algebraMap ℝ R).comp (algebraMap ℚ ℝ) :=
      Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* R => f c) this
  set V : Submodule ℝ (Fin n → R) :=
    Submodule.span ℝ (Set.range fun k => (fun i => τ (u k i))) with hV
  have h1 : ∀ x : Fin n → E, (fun i => τ (x i)) ∈ V := by
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range u) := by rw [hu]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero =>
      have : (fun i => τ ((0 : Fin n → E) i)) = 0 := by ext i; simp
      rw [this]; exact V.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => τ ((x + y) i)) = (fun i => τ (x i)) + (fun i => τ (y i)) := by
        ext i; simp
      rw [this]; exact V.add_mem hx hy
    | smul c x _ hx =>
      have : (fun i => τ ((c • x) i)) = (algebraMap ℚ ℝ c) • (fun i => τ (x i)) := by
        ext i
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, hq]
      rw [this]; exact V.smul_mem _ hx
  have h2 : ∀ (i : Fin n) (r : R), Pi.single i r ∈ V := by
    intro i r
    have hle : Submodule.span ℝ (Set.range τ) ≤
        V.comap (LinearMap.single ℝ (fun _ : Fin n => R) i) := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      have := h1 (Pi.single i e)
      have h' : (fun j => τ ((Pi.single i e : Fin n → E) j)) = Pi.single i (τ e) := by
        ext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      rw [h'] at this
      exact this
    have hr : r ∈ Submodule.span ℝ (Set.range τ) := by rw [hτ]; trivial
    exact hle hr
  have h3 : ∀ y : Fin n → R, y ∈ V := by
    intro y
    rw [← Finset.univ_sum_single y]
    exact V.sum_mem fun i _ => h2 i _
  let φ : (Fin n → R) →ₗ[ℝ] (Fin n → R) :=
    { toFun := fun v => v ᵥ* g.1
      map_add' := fun v w => Matrix.add_vecMul _ _ _
      map_smul' := fun c v => Matrix.smul_vecMul _ _ _ }
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro y _
    have hy : y = φ (y ᵥ* (g⁻¹).1) := by
      simp [φ, Matrix.vecMul_vecMul]
    have hm : φ (y ᵥ* (g⁻¹).1) ∈ V.map φ := Submodule.mem_map_of_mem (h3 _)
    rw [hV, Submodule.map_span, ← Set.range_comp] at hm
    rw [hy]
    exact hm
  · rw [hcard, Module.finrank_pi_fintype, ← hrk]
    simp [mul_comm]

end GlobalTheory
