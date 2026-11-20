import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

/- English proof (translation)
Use extensionality with `T`. Simplify using `only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]`. Use `noncomm_ring`.
-/
theorem adj_sub_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) : adj (x - y) = adj x - adj y := by
  ext T
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  noncomm_ring

/- English proof (translation)
Use extensionality with `T`. Simplify using `[adj]`.
-/
theorem adj_zero_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] : adj (0 : A) = 0 := by
  ext T
  simp [adj]

/- English proof (translation)
Use extensionality with `T`. Simplify using `only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_sub]`. Use `noncomm_ring`.
-/
theorem adj_commutator_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) :
    adj x * adj y - adj y * adj x = adj (x * y - y * x) := by
  ext T
  simp only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    map_sub]
  noncomm_ring

/- English proof (translation)
Introduce `V _ _ N K e hrel hbdd hspan`. Prove the components needed by the constructor for the conclusion. Introduce `a b c d ha hb hc hd`. Rewrite using `[adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]`. Apply the tactic sequence `split_ifs <;> simp [adj_zero_of_adjBdd]`.

Introduce `a ha b hb n T hT hn`. Establish `hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x`. Introduce and unpack `x ⟨μ, hμ⟩`. Simplify using `only [LinearMap.zero_apply]`. Distinguish the cases in `hx : x = 0`.

Simplify using `[hx]`. Establish `h1 : μ b - μ a ≤ K`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Apply `hx` to reduce the goal to its premises.

Apply `hbdd b hb a ha (μ b - μ a) x _ hlt` to reduce the goal to its premises. Rewrite using `[hμ b hb, hμ a ha]`. Use `push_cast`. Rewrite using `[sub_smul]`. Apply `hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)` to reduce the goal to its premises.

Establish `eq` using `LinearMap.congr_fun hT x`. Simplify using `only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq`. Use `push_cast`. Rewrite using `[add_smul, sub_smul, ← eq]`. Normalize the expressions using the abelian group laws.

Conclude with `LinearMap.ext_on hspan hw`.
-/
theorem adjBdd_holds : AdjBdd := by
  intro V _ _ N K e hrel hbdd hspan
  constructor
  · intro a b c d ha hb hc hd
    rw [adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]
    split_ifs <;> simp [adj_zero_of_adjBdd]
  · intro a ha b hb n T hT hn
    have hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x := by
      rintro x ⟨μ, hμ⟩
      simp only [LinearMap.zero_apply]
      by_cases hx : x = 0
      · simp [hx]
      have h1 : μ b - μ a ≤ K := by
        by_contra hlt
        push_neg at hlt
        apply hx
        apply hbdd b hb a ha (μ b - μ a) x _ hlt
        rw [hμ b hb, hμ a ha]
        push_cast
        rw [sub_smul]
      apply hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)
      have eq := LinearMap.congr_fun hT x
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq
      push_cast
      rw [add_smul, sub_smul, ← eq]
      abel
    exact LinearMap.ext_on hspan hw

end GlobalTheory.LeviCut
