import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Introduce `k L Ω _ _ _ _ _ _ _ _ _ _ _ l _`. Establish `hcl : IsClosed (galOf k L Ω : Set (G k Ω))` using `Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1`. Establish `hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g` using `fun g => DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g`. Establish `hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤`. Distinguish the cases in `h : l = 2`.

Substitute `h` using the available equality. Use `or_congr_right ?_` and prove the remaining obligations. Rewrite using `[← range_galEmb]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h _ ⟨g, rfl⟩`.

Use `⟨trivial, ?_⟩` and prove the remaining obligations. Use `show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2`. Rewrite using `[hχ]`. Conclude with `h g`. Introduce `h g`.

Establish `h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2` using `(h ⟨g, rfl⟩).2`. Rewrite `h'` using `[hχ]`. Conclude with `h'`. Conclude with `⟨fun _ => Or.inl h, fun _ => Or.inl h⟩`. Conclude with `⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩`.
-/
theorem UpperTheory.V.Tower.genGal :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], IsClosed (galOf k L Ω : Set (G k Ω)) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤) ∧
        (Procyc L Ω l → ∃ γ, IsGen l (galOf k L Ω) γ) := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hcl : IsClosed (galOf k L Ω : Set (G k Ω)) :=
    Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1
  have hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g := fun g =>
    DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g
  have hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤ := by
    by_cases h : l = 2
    · subst h
      refine or_congr_right ?_
      rw [← range_galEmb]
      constructor
      · rintro h _ ⟨g, rfl⟩
        refine ⟨trivial, ?_⟩
        show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [hχ]
        exact h g
      · intro h g
        have h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2 := (h ⟨g, rfl⟩).2
        rw [hχ] at h'
        exact h'
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  exact ⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩
