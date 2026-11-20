import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `B _ _ _ W W' _ h h' hhh hW T hT hcomm`. Set `S : W →ₗ[ℂ] W` to `{ toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩ map_add' := fun f g => by ext; simp [mul_add] map_smul' := fun c f => by ext; simp [mul_smul_comm] }`. Use `haveI : Nontrivial W := by`. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`.

Apply `hT` to reduce the goal to its premises. Use extensionality with `f`. Rewrite using `[Subsingleton.elim f 0]`. Simplify using the standard rewrite rules. Take `⟨a, ha⟩` from `Module.End.exists_eigenvalue S`.

Take `⟨f₀, hf₀⟩` from `ha.exists_hasEigenvector`. Establish `hS : S f₀ = a • f₀` using `hf₀.apply_eq_smul`. Establish `h0 : (T f₀ : B) = a • (h * (f₀ : B))`. Establish `hc : h' * (T f₀ : B) = a • (f₀ : B)`. Use `congrArg (fun x : W => (x : B)) hS` as an intermediate fact.

Simplify `this` using `[S]`. Combine the equalities or inequalities in the displayed calculation. Use `_ = h * (a • (f₀ : B)) := by rw [hc]`. Use `_ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _`. Establish `hf0ne : (f₀ : B) ≠ 0`.

Introduce `hz`. Conclude with `hf₀.2 (Subtype.ext hz)`. Establish `key : ∀ f : W, (T f : B) = a • (h * (f : B))`. Introduce `f`. Establish `hx` using `hcomm f f₀`.

Rewrite `hx` using `[h0]`. Apply `mul_right_cancel₀ hf0ne` to reduce the goal to its premises. Rewrite using `[hx]`. Simplify using `only [Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨a, ?_, key⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hT` to reduce the goal to its premises. Use extensionality with `f`. Simplify using `[key f]`.
-/
theorem commuting_map_eq_smul_multiplier :
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] (W W' : Submodule ℂ B) [FiniteDimensional ℂ W] (h h' : B), h * h' = 1 → (∀ w ∈ W', h' * w ∈ W) → ∀ T : W →ₗ[ℂ] W', T ≠ 0 → (∀ f g : W, (T f : B) * (g : B) = (f : B) * (T g : B)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : W, (T f : B) = a • (h * (f : B)) := by
  intro B _ _ _ W W' _ h h' hhh hW T hT hcomm
  let S : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩
      map_add' := fun f g => by ext; simp [mul_add]
      map_smul' := fun c f => by ext; simp [mul_smul_comm] }
  haveI : Nontrivial W := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT
    ext f
    rw [Subsingleton.elim f 0]
    simp
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue S
  obtain ⟨f₀, hf₀⟩ := ha.exists_hasEigenvector
  have hS : S f₀ = a • f₀ := hf₀.apply_eq_smul
  have h0 : (T f₀ : B) = a • (h * (f₀ : B)) := by
    have hc : h' * (T f₀ : B) = a • (f₀ : B) := by
      have := congrArg (fun x : W => (x : B)) hS
      simpa [S] using this
    calc (T f₀ : B) = h * (h' * T f₀) := by rw [← mul_assoc, hhh, one_mul]
    _ = h * (a • (f₀ : B)) := by rw [hc]
    _ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _
  have hf0ne : (f₀ : B) ≠ 0 := by
    intro hz
    exact hf₀.2 (Subtype.ext hz)
  have key : ∀ f : W, (T f : B) = a • (h * (f : B)) := by
    intro f
    have hx := hcomm f f₀
    rw [h0] at hx
    apply mul_right_cancel₀ hf0ne
    rw [hx]
    simp only [Algebra.smul_def]
    ring
  refine ⟨a, ?_, key⟩
  rintro rfl
  apply hT
  ext f
  simp [key f]

end GlobalTheory
