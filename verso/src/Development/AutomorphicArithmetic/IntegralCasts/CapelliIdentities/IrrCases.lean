import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative.
-/
theorem UpperTheory.Reformulated.B.Qe20.irrCases :
    ∀ {G V : Type} [inst : Group G]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V),
    ρ.IsIrreducible →
      ∀ (W : Submodule ℂ V), (∀ (g : G), ∀ v ∈ W, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G V _ _ _ ρ hρ W hW
  let S : Subrepresentation ρ := ⟨W, fun g v hv => hW g v hv⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
