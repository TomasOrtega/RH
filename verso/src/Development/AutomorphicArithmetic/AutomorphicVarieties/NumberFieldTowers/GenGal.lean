import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
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
