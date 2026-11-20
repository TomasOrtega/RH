import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ s`. Use `haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic`. Use `set K := IntermediateField.adjoin E (s : Set Ω) with hK`. Use `haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Take `⟨α, hα⟩` from `Field.exists_primitive_element E K`.

Use `⟨(α : Ω), fun σ => ?_⟩` and prove the remaining obligations. Establish `key : IntermediateField.adjoin E {(α : Ω)} = K`. Establish `h1` using `congrArg (IntermediateField.map K.val) hα`. Rewrite `h1` using `[IntermediateField.adjoin_map]`. Establish `hm : IntermediateField.map K.val ⊤ = K`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, -, rfl⟩`. Conclude with `z.2`. Introduce `hy`.

Conclude with `⟨⟨y, hy⟩, trivial, rfl⟩`. Rewrite `h1` using `[hm]`. Simplify `h1` using `[Set.image_singleton]`. Establish `gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y`. Introduce `T hT y hy`.

Use `IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val) (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])` as an intermediate fact. Conclude with `congrArg (fun φ => φ ⟨y, hy⟩) this`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `hxK : x ∈ IntermediateField.adjoin E {(α : Ω)}`.

Rewrite using `[key]`. Conclude with `IntermediateField.subset_adjoin E _ hx`. Conclude with `gen {(α : Ω)} (by simpa using h) x hxK`. Introduce `h`. Conclude with `gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2`.
-/
theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
