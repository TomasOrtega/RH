import Mathlib

open NumberField

/- English proof (translation)
Introduce `K _ _ _ h`. Use `choose c hc using h`. Set `φ₀ : K →+* ℂ` to `Classical.choice inferInstance`. Establish `hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K`. Introduce `x`.

Rewrite using `[mem_maximalRealSubfield_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx φ`. Use `hc x φ` as an intermediate fact. Rewrite `this` using `[hx]`.

Conclude with `this.symm`. Introduce `hx`. Apply `φ₀.injective` to reduce the goal to its premises. Rewrite using `[hc]`. Conclude with `hx φ₀`.

Establish `hinv : ∀ x : K, c (c x) = x`. Introduce `x`. Apply `φ₀.injective` to reduce the goal to its premises. Simplify using `[hc]`. Set `σ : K ≃ₐ[maximalRealSubfield K] K` to `{ toFun := c invFun := c left_inv := hinv right_inv := hinv map_mul' := fun x y => φ₀.injective (by simp [hc]) map_add' := fun x y => φ₀.injective (by simp [hc]) commutes' := fun x => (hfix _).mpr x.2 }`.

Establish `hσ : ∀ x, σ x = c x` using `fun _ => rfl`. Establish `hne : σ ≠ 1`. Introduce `h1`. Apply `IsTotallyComplex.complexEmbedding_not_isReal φ₀` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `hx : c x = x` using `by rw [← hσ, h1]; rfl`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hc, hx]`. Establish `hord : orderOf σ = 2` using `orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne`. Establish `hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥`.

Use `le_antisymm (fun x hx => ?_) bot_le` and prove the remaining obligations. Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Conclude with `IntermediateField.mem_bot.mpr ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩`. Establish `hrank` using `IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)`. Rewrite `hrank` using `[hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord]`.

Establish `: Algebra.IsQuadraticExtension (maximalRealSubfield K) K` using `⟨hrank⟩`. Conclude with `⟨⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh9.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice inferInstance
  have hfix : ∀ x : K, c x = x ↔ x ∈ maximalRealSubfield K := by
    intro x
    rw [mem_maximalRealSubfield_iff]
    constructor
    · intro hx φ
      have := hc x φ
      rw [hx] at this
      exact this.symm
    · intro hx
      apply φ₀.injective
      rw [hc]
      exact hx φ₀
  have hinv : ∀ x : K, c (c x) = x := by
    intro x
    apply φ₀.injective
    simp [hc]
  let σ : K ≃ₐ[maximalRealSubfield K] K :=
    { toFun := c
      invFun := c
      left_inv := hinv
      right_inv := hinv
      map_mul' := fun x y => φ₀.injective (by simp [hc])
      map_add' := fun x y => φ₀.injective (by simp [hc])
      commutes' := fun x => (hfix _).mpr x.2 }
  have hσ : ∀ x, σ x = c x := fun _ => rfl
  have hne : σ ≠ 1 := by
    intro h1
    apply IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x = x := by rw [← hσ, h1]; rfl
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, hx]
  have hord : orderOf σ = 2 :=
    orderOf_eq_prime (by ext x; simp [pow_two, hσ, hinv]) hne
  have hbot : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.mpr
      ⟨⟨x, (hfix x).mp (hx σ (Subgroup.mem_zpowers σ))⟩, rfl⟩
  have hrank := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers, hord] at hrank
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := ⟨hrank⟩
  exact ⟨⟩
