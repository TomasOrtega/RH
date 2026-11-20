import Mathlib

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `V _ _ T p hcomm hp`. Use `set A := Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) with hA`. Set `X' : Set (Module.End ℂ V → ℂ)` to `{χ | (∀ z, z ∉ A → χ z = 0) ∧ (∃ u : V, u ≠ 0 ∧ ∀ z ∈ A, z u = χ z • u) ∧ ∀ t ∈ T, (p t).eval (χ t) = 0}`. Establish `hdet : ∀ χ₁ ∈ X', ∀ χ₂ ∈ X', (∀ t ∈ T, χ₁ t = χ₂ t) → χ₁ = χ₂`. Introduce and unpack `χ₁ ⟨h₁0, ⟨u₁, hu₁, he₁⟩, -⟩ χ₂ ⟨h₂0, ⟨u₂, hu₂, he₂⟩, -⟩ hT`.

Establish `key : ∀ (χ : Module.End ℂ V → ℂ) (u : V), u ≠ 0 → (∀ z ∈ A, z u = χ z • u) → (∀ r : ℂ, χ (algebraMap ℂ _ r) = r) ∧ (∀ x ∈ A, ∀ y ∈ A, χ (x + y) = χ x + χ y) ∧ (∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y)`. Introduce `χ u hu he`. Establish `inj` using `smul_left_injective ℂ hu`. Use `⟨fun r => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩` and prove the remaining obligations. Apply `inj` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← he _ (Subalgebra.algebraMap_mem A r)]`. Simplify using `[Module.algebraMap_end_apply]`. Apply `inj` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[← he _ (add_mem hx hy), LinearMap.add_apply, he x hx, he y hy, add_smul]`. Apply `inj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← he _ (mul_mem hx hy), Module.End.mul_apply, he y hy, map_smul, he x hx, smul_smul, mul_comm]`. Take `⟨m₁, a₁, p₁⟩` from `key χ₁ u₁ hu₁ he₁`.

Take `⟨m₂, a₂, p₂⟩` from `key χ₂ u₂ hu₂ he₂`. Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z ∈ A`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hT x hx`.

Consider the case `algebraMap r => rw [m₁, m₂]`. Consider the case `add x y hx hy ihx ihy => rw [a₁ x hx y hy, a₂ x hx y hy, ihx, ihy]`. Consider the case `mul x y hx hy ihx ihy => rw [p₁ x hx y hy, p₂ x hx y hy, ihx, ihy]`. Rewrite using `[h₁0 z hz, h₂0 z hz]`. Use `⟨X', ?_, ?_⟩` and prove the remaining obligations.

Set `f : (Module.End ℂ V → ℂ) → (T → ℂ)` to `fun χ t => χ t`. Apply `Set.Finite.of_finite_image (f := f)` to reduce the goal to its premises. Apply `(Set.Finite.pi (t := fun t : T => ((p t).roots.toFinset : Set ℂ)) (fun t => Finset.finite_toSet _)).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨χ, ⟨-, -, hroot⟩, rfl⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, Finset.mem_coe, Multiset.mem_toFinset, true_implies]`.

Introduce `t`. Rewrite using `[Polynomial.mem_roots (hp t t.2)]`. Conclude with `hroot t t.2`. Introduce `χ₁ h₁ χ₂ h₂ hf`. Conclude with `hdet χ₁ h₁ χ₂ h₂ fun t ht => congrFun hf ⟨t, ht⟩`.

Introduce `ψ hψ χ' u hu hu0 he`. Use `⟨fun z => if z ∈ A then χ' z else 0, ⟨fun z hz => if_neg hz, ⟨u, hu0, fun z hz => by simp only [if_pos hz]; exact he z hz⟩, fun t ht => ?_⟩, fun z hz => (if_pos hz).symm⟩` and prove the remaining obligations. Establish `htA : t ∈ A` using `Algebra.subset_adjoin ht`. Simplify using `only [if_pos htA]`. Establish `hker : u ∈ LinearMap.ker (Polynomial.aeval t (p t))`.

Use `(Submodule.span_le.mpr ?_) hu` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hzt : Commute t z` using `Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz (fun s hs => hcomm t ht s hs)`. Establish `hc : Commute z (Polynomial.aeval t (p t))` using `Algebra.commute_of_mem_adjoin_singleton_of_commute (Polynomial.aeval_mem_adjoin_singleton ℂ t) hzt.symm`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker]`.

Rewrite using `[← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hψ t ht, map_zero]`. Establish `hev : t.HasEigenvector (χ' t) u` using `Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he t htA), hu0⟩`. Use `Module.End.aeval_apply_of_hasEigenvector (p := p t) hev` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker.mp hker]`. Conclude with `smul_left_injective ℂ hu0 (by simpa using this.symm)`.
-/
theorem eigencharacters_finite_of_commuting_annihilated :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V))
      (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) →
      (∀ t ∈ T, p t ≠ 0) → ∃ X' : Set (Module.End ℂ V → ℂ), X'.Finite ∧ ∀ ψ : V,
        (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → ∀ (χ' : Module.End ℂ V → ℂ) (u : V),
        u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) ''
          (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V))) → u ≠ 0 →
        (∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), z u = χ' z • u) →
        ∃ χ ∈ X', ∀ z ∈ Algebra.adjoin ℂ (T : Set (Module.End ℂ V)), χ' z = χ z := by
  intro V _ _ T p hcomm hp
  classical
  set A := Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) with hA
  let X' : Set (Module.End ℂ V → ℂ) :=
    {χ | (∀ z, z ∉ A → χ z = 0) ∧ (∃ u : V, u ≠ 0 ∧ ∀ z ∈ A, z u = χ z • u) ∧
      ∀ t ∈ T, (p t).eval (χ t) = 0}

  have hdet : ∀ χ₁ ∈ X', ∀ χ₂ ∈ X', (∀ t ∈ T, χ₁ t = χ₂ t) → χ₁ = χ₂ := by
    rintro χ₁ ⟨h₁0, ⟨u₁, hu₁, he₁⟩, -⟩ χ₂ ⟨h₂0, ⟨u₂, hu₂, he₂⟩, -⟩ hT

    have key : ∀ (χ : Module.End ℂ V → ℂ) (u : V), u ≠ 0 → (∀ z ∈ A, z u = χ z • u) →
        (∀ r : ℂ, χ (algebraMap ℂ _ r) = r) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x + y) = χ x + χ y) ∧
        (∀ x ∈ A, ∀ y ∈ A, χ (x * y) = χ x * χ y) := by
      intro χ u hu he
      have inj := smul_left_injective ℂ hu
      refine ⟨fun r => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
      · apply inj
        simp only
        rw [← he _ (Subalgebra.algebraMap_mem A r)]
        simp [Module.algebraMap_end_apply]
      · apply inj
        simp only
        rw [← he _ (add_mem hx hy), LinearMap.add_apply, he x hx, he y hy, add_smul]
      · apply inj
        simp only
        rw [← he _ (mul_mem hx hy), Module.End.mul_apply, he y hy, map_smul, he x hx,
          smul_smul, mul_comm]
    obtain ⟨m₁, a₁, p₁⟩ := key χ₁ u₁ hu₁ he₁
    obtain ⟨m₂, a₂, p₂⟩ := key χ₂ u₂ hu₂ he₂
    funext z
    by_cases hz : z ∈ A
    · induction hz using Algebra.adjoin_induction with
      | mem x hx => exact hT x hx
      | algebraMap r => rw [m₁, m₂]
      | add x y hx hy ihx ihy => rw [a₁ x hx y hy, a₂ x hx y hy, ihx, ihy]
      | mul x y hx hy ihx ihy => rw [p₁ x hx y hy, p₂ x hx y hy, ihx, ihy]
    · rw [h₁0 z hz, h₂0 z hz]
  refine ⟨X', ?_, ?_⟩
  ·
    let f : (Module.End ℂ V → ℂ) → (T → ℂ) := fun χ t => χ t
    apply Set.Finite.of_finite_image (f := f)
    · apply (Set.Finite.pi (t := fun t : T => ((p t).roots.toFinset : Set ℂ))
        (fun t => Finset.finite_toSet _)).subset
      rintro _ ⟨χ, ⟨-, -, hroot⟩, rfl⟩
      simp only [Set.mem_pi, Set.mem_univ, Finset.mem_coe, Multiset.mem_toFinset, true_implies]
      intro t
      rw [Polynomial.mem_roots (hp t t.2)]
      exact hroot t t.2
    · intro χ₁ h₁ χ₂ h₂ hf
      exact hdet χ₁ h₁ χ₂ h₂ fun t ht => congrFun hf ⟨t, ht⟩
  · intro ψ hψ χ' u hu hu0 he
    refine ⟨fun z => if z ∈ A then χ' z else 0, ⟨fun z hz => if_neg hz,
      ⟨u, hu0, fun z hz => by simp only [if_pos hz]; exact he z hz⟩, fun t ht => ?_⟩,
      fun z hz => (if_pos hz).symm⟩
    have htA : t ∈ A := Algebra.subset_adjoin ht
    simp only [if_pos htA]

    have hker : u ∈ LinearMap.ker (Polynomial.aeval t (p t)) := by
      refine (Submodule.span_le.mpr ?_) hu
      rintro _ ⟨z, hz, rfl⟩
      have hzt : Commute t z :=
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz (fun s hs => hcomm t ht s hs)
      have hc : Commute z (Polynomial.aeval t (p t)) :=
        Algebra.commute_of_mem_adjoin_singleton_of_commute
          (Polynomial.aeval_mem_adjoin_singleton ℂ t) hzt.symm
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hψ t ht, map_zero]
    have hev : t.HasEigenvector (χ' t) u :=
      Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (he t htA), hu0⟩
    have := Module.End.aeval_apply_of_hasEigenvector (p := p t) hev
    rw [LinearMap.mem_ker.mp hker] at this
    exact smul_left_injective ℂ hu0 (by simpa using this.symm)

end GlobalTheory
