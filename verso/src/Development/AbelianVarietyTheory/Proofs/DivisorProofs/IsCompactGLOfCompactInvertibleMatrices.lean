import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem isCompact_GL_of_invSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)),
    IsCompact T → T ⊆ invSet E n →
      IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  intro E _ _ n T hT hsub
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have hu : Continuous fun p : T =>
      (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := (GlobalTheory.ConstTermSmooth.contDiffOn_invM (E := E) (a := n)).continuousOn.comp_continuous
      (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  convert isCompact_range hu using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩
  · rintro ⟨p, rfl⟩
    exact p.2

end GlobalTheory.WhitBump
