import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocity
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerCochainEqDlogExplicitReciprocity.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∃ x ∈ A, ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) s k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ * (Polynomial.derivative P).eval ζ / P.eval ζ)) + (s x - x)) := by
  first | exact @GlobalTheory.RecOne.kummer_eq_dlog_one | exact GlobalTheory.RecOne.kummer_eq_dlog_one | (intros; apply GlobalTheory.RecOne.kummer_eq_dlog_one <;> assumption)
