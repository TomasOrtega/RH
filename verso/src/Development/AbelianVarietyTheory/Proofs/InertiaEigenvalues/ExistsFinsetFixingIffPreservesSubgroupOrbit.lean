import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic`. Establish `hint : IsIntegral E y` using `Algebra.IsIntegral.isIntegral y`. Use `set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef`. Establish `hS : S.Finite`. Use `((minpoly E y).rootSet_finite Ω).subset ?_` and prove the remaining obligations.

Introduce and unpack `t ⟨τ, -, rfl⟩`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero hint, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_algEquiv]`. Simplify using `[minpoly.aeval]`.

Use `set O := hS.toFinset with hOdef`. Establish `hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t` using `fun t => by simp [O, S]`. Use `set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP`. Use `⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩` and prove the remaining obligations. Establish `key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔ P.map (σ : Ω →+* Ω) = P`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `n`. Rewrite using `[coeff_map]`. Distinguish the cases in `hn : n ≤ P.natDegree`.

Conclude with `h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]`. Simplify using the standard rewrite rules. Introduce `h x hx`. Take `⟨n, -, rfl⟩` from `Finset.mem_image.1 hx`.

Use `congrArg (fun p => p.coeff n) h` as an intermediate fact. Simplify `this` using `[coeff_map]`. Establish `hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t))`. Simplify using `[hP, Polynomial.map_prod]`. Rewrite using `[key, hmap]`.

Prove the components needed by the constructor for the conclusion. Introduce `h τ hτ`. Establish `h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0`. Rewrite using `[eval_prod]`. Conclude with `Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)`.

Rewrite `h0` using `[h, hP, eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨t, ht, ht0⟩` from `h0`. Take `⟨τ', hτ', rfl⟩` from `(hmemO t).1 ht`. Use `⟨τ', hτ', ?_⟩` and prove the remaining obligations. Simplify `ht0` using `[sub_eq_zero]`.

Introduce `h`. Establish `hinj : Function.Injective (σ : Ω → Ω)` using `σ.injective`. Establish `hsub : O.image σ ⊆ O`. Introduce `u hu`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hu`.

Take `⟨τ, hτ, rfl⟩` from `(hmemO t).1 ht`. Take `⟨τ', hτ', he⟩` from `h τ hτ`. Conclude with `(hmemO _).2 ⟨τ', hτ', he.symm⟩`. Establish `heq : O.image σ = O` using `Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_image (fun a _ b _ hab => hinj hab)]`. Use `_ = P := by rw [heq]`.
-/
theorem orbit_stab_cut_finite (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω) :
    ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  classical
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set S : Set Ω := {t | ∃ τ ∈ H, τ y = t} with hSdef
  have hS : S.Finite := by
    refine ((minpoly E y).rootSet_finite Ω).subset ?_
    rintro t ⟨τ, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algEquiv]
    simp [minpoly.aeval]
  set O := hS.toFinset with hOdef
  have hmemO : ∀ t, t ∈ O ↔ ∃ τ ∈ H, τ y = t := fun t => by simp [O, S]
  set P : Polynomial Ω := ∏ t ∈ O, (X - C t) with hP
  refine ⟨(Finset.range (P.natDegree + 1)).image P.coeff, fun σ => ?_⟩
  have key : (∀ x ∈ (Finset.range (P.natDegree + 1)).image P.coeff, σ x = x) ↔
      P.map (σ : Ω →+* Ω) = P := by
    constructor
    · intro h
      ext n
      rw [coeff_map]
      by_cases hn : n ≤ P.natDegree
      · exact h _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hn)]; simp
    · intro h x hx
      obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hx
      have := congrArg (fun p => p.coeff n) h
      simpa [coeff_map] using this
  have hmap : P.map (σ : Ω →+* Ω) = ∏ t ∈ O, (X - C (σ t)) := by
    simp [hP, Polynomial.map_prod]
  rw [key, hmap]
  constructor
  · intro h τ hτ
    have h0 : (∏ t ∈ O, (X - C (σ t))).eval (σ (τ y)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero ((hmemO _).2 ⟨τ, hτ, rfl⟩) (by simp)
    rw [h, hP, eval_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨t, ht, ht0⟩ := h0
    obtain ⟨τ', hτ', rfl⟩ := (hmemO t).1 ht
    refine ⟨τ', hτ', ?_⟩
    simpa [sub_eq_zero] using ht0
  · intro h
    have hinj : Function.Injective (σ : Ω → Ω) := σ.injective
    have hsub : O.image σ ⊆ O := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨τ, hτ, rfl⟩ := (hmemO t).1 ht
      obtain ⟨τ', hτ', he⟩ := h τ hτ
      exact (hmemO _).2 ⟨τ', hτ', he.symm⟩
    have heq : O.image σ = O :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
    calc ∏ t ∈ O, (X - C (σ t)) = ∏ u ∈ O.image σ, (X - C u) :=
          by
          rw [Finset.prod_image (fun a _ b _ hab => hinj hab)]
      _ = P := by rw [heq]

end GlobalTheory
