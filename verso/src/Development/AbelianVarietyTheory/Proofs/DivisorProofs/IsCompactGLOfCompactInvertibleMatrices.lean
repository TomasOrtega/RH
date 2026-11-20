import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

/- English proof (translation)
Introduce `E _ _ n T hT hsub`. Use `haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT`. Establish `hu : Continuous fun p : T => (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E))`. Use `Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.ConstTermSmooth.contDiffOn_invM (E := E) (a := n)).continuousOn.comp_continuous (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2` as an intermediate fact.

Use `Continuous.congr this fun p => ?_` and prove the remaining obligations. Simplify using `only [Matrix.coe_units_inv]`. Both sides reduce to the same expression. Use `isCompact_range hu using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩`. Introduce and unpack `⟨p, rfl⟩`. Conclude with `p.2`.
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
