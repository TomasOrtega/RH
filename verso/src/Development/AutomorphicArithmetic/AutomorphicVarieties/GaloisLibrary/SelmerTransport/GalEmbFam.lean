import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Introduce `k E Ω _ _ _ _ _ _ _ _ _ _ _ l _`. Establish `hD : ∀ A : ValuationSubring Ω, (Dec (F` using `k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by`. Use extensionality with `σ`. Rewrite using `[Subgroup.mem_comap, mem_Dec, mem_Dec]`. Conclude with `Iff.rfl`.

Establish `hI : ∀ A : ValuationSubring Ω, (Ine (F` using `k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by`. Use extensionality with `σ`. Rewrite using `[Subgroup.mem_comap]`. Conclude with `and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl`. Use `⟨fun A => ⟨hD A, hI A⟩, ?_, ?_, fun e => ?_⟩` and prove the remaining obligations.

Use extensionality with `D`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨D', ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩`. Conclude with `Or.inl ⟨A, hl, hD A⟩`. Conclude with `Or.inr ⟨A, hI A⟩`.

Introduce and unpack `(⟨A, hl, rfl⟩ | ⟨A, rfl⟩)`. Conclude with `⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩`. Conclude with `⟨_, Or.inr ⟨A, rfl⟩, hI A⟩`. Conclude with `MonoidHom.ext fun _ => rfl`. Conclude with `MonoidHom.ext fun _ => rfl`.
-/
theorem UpperTheory.V.Base.galEmbFam :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime],
      (∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A ∧ (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A) ∧
      Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l = shaFam E Ω l ∧ (cycZ k Ω l).comp (galEmb k E Ω) = cycZ E Ω l ∧
      ∀ e : ℤ, (LDataCardLeFinrank.qzG k Ω l e).comp (galEmb k E Ω) = LDataCardLeFinrank.qzG E Ω l e := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hD : ∀ A : ValuationSubring Ω, (Dec (F := k) A).comap (galEmb k E Ω) = Dec (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap, mem_Dec, mem_Dec]
    exact Iff.rfl
  have hI : ∀ A : ValuationSubring Ω, (Ine (F := k) A).comap (galEmb k E Ω) = Ine (F := E) A := fun A => by
    ext σ
    rw [Subgroup.mem_comap]
    exact and_congr (SetLike.ext_iff.1 (hD A) σ) Iff.rfl
  refine ⟨fun A => ⟨hD A, hI A⟩, ?_, ?_, fun e => ?_⟩
  · ext D
    constructor
    · rintro ⟨D', ⟨A, hl, rfl⟩ | ⟨A, rfl⟩, rfl⟩
      · exact Or.inl ⟨A, hl, hD A⟩
      · exact Or.inr ⟨A, hI A⟩
    · rintro (⟨A, hl, rfl⟩ | ⟨A, rfl⟩)
      · exact ⟨_, Or.inl ⟨A, hl, rfl⟩, hD A⟩
      · exact ⟨_, Or.inr ⟨A, rfl⟩, hI A⟩
  · exact MonoidHom.ext fun _ => rfl
  · exact MonoidHom.ext fun _ => rfl
