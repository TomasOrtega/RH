import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.PowFix

/- English proof (translation)
Establish `hfin : ((minpoly E x).rootSet Ω).Finite` using `Polynomial.rootSet_finite _ _`. Use `haveI := hfin.to_subtype`. Set `f : ℕ → (minpoly E x).rootSet Ω` to `fun n => ⟨(σ ^ n) x, by`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩`. Take `⟨a, b, hab, h⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Establish `h' : (σ ^ a) x = (σ ^ b) x` using `congrArg Subtype.val h`. Establish `key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x`. Introduce `a b hlt he`.

Use `⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩` and prove the remaining obligations. Establish `e : σ ^ b = σ ^ a * σ ^ (b - a)` using `by rw [← pow_add, Nat.add_sub_cancel' hlt.le]`. Rewrite `he` using `[e, AlgEquiv.mul_apply]`. Conclude with `((σ ^ a).injective he).symm`. Break down `lt_or_gt_of_ne hab with hlt | hlt` into its components or cases.

Conclude with `key a b hlt h'`. Conclude with `key b a hlt h'.symm`.
-/
theorem exists_pos_pow_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  classical
  have hfin : ((minpoly E x).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  haveI := hfin.to_subtype
  let f : ℕ → (minpoly E x).rootSet Ω := fun n => ⟨(σ ^ n) x, by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    rw [show ((σ ^ n) x) = ((σ ^ n : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) x from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨a, b, hab, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h' : (σ ^ a) x = (σ ^ b) x := congrArg Subtype.val h
  have key : ∀ a b : ℕ, a < b → (σ ^ a) x = (σ ^ b) x → ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    intro a b hlt he
    refine ⟨b - a, Nat.sub_pos_of_lt hlt, ?_⟩
    have e : σ ^ b = σ ^ a * σ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [e, AlgEquiv.mul_apply] at he
    exact ((σ ^ a).injective he).symm
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt h'
  · exact key b a hlt h'.symm

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rfl`. Consider the case `succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]`.
-/
theorem pow_apply_eq_of_apply_eq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (τ : Ω ≃ₐ[E] Ω) (x : Ω) (h : τ x = x) (j : ℕ) : (τ ^ j) x = x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ σ s`. Establish `hint : ∀ x : Ω, IsIntegral E x` using `fun x => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral`. Use `choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)`. Use `⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem k hx`.

Rewrite using `[hc, pow_mul]`. Conclude with `pow_apply_eq_of_apply_eq _ x (hk x) c`.
-/
theorem exists_pos_pow_fix : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c

end GlobalTheory.PowFix
