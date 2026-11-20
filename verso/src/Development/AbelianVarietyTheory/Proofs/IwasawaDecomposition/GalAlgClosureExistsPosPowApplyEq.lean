import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ σ t`. Establish `hint : IsIntegral E t` using `((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral`. Establish `hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω`. Introduce `i`. Rewrite using `[Polynomial.mem_rootSet]`.

Use `⟨minpoly.ne_zero hint, ?_⟩` and prove the remaining obligations. Establish `h` using `Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)`. Rewrite `h` using `[minpoly.aeval, map_zero]`. Conclude with `h`. Use `haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype`.

Take `⟨i, j, hij, heq⟩` from `Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))`. Establish `heq' : (σ ^ i) t = (σ ^ j) t` using `congrArg Subtype.val heq`. Establish `key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t`. Introduce `a b hab h`. Use `⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩` and prove the remaining obligations.

Apply `(σ ^ a).injective` to reduce the goal to its premises. Rewrite using `[← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]`. Conclude with `h.symm`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases. Conclude with `key i j h heq'`.

Conclude with `key j i h heq'.symm`.
-/
theorem galAlgClosure_exists_pos_pow_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (σ : G E Ω) (t : Ω), ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
  intro E Ω _ _ _ _ _ σ t
  have hint : IsIntegral E t :=
    ((IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic t).isIntegral
  have hmem : ∀ i : ℕ, (σ ^ i) t ∈ (minpoly E t).rootSet Ω := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ i : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    rw [minpoly.aeval, map_zero] at h
    exact h
  haveI : Finite ((minpoly E t).rootSet Ω) := ((minpoly E t).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨(σ ^ i) t, hmem i⟩ : (minpoly E t).rootSet Ω))
  have heq' : (σ ^ i) t = (σ ^ j) t := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → (σ ^ a) t = (σ ^ b) t → ∃ k : ℕ, 0 < k ∧ (σ ^ k) t = t := by
    intro a b hab h
    refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
    apply (σ ^ a).injective
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

end GlobalTheory
