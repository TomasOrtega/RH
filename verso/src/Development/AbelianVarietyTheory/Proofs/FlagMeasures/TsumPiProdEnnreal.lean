import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Introduce `ι _`. Use `Fintype.induction_empty_option (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞), ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι` and prove the remaining obligations. Introduce `α β _ e h X φ`. Use `letI : Fintype α := Fintype.ofEquiv β e.symm`. Establish `h1` using `h (X := fun a => X (e a)) (fun a => φ (e a))`.

Rewrite using `[← (Equiv.piCongrLeft X e).tsum_eq]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `x`. Rewrite using `[← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a))) (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]`.

Simplify using `only [Equiv.piCongrLeft_apply_apply]`. Use `_ = ∏ a, ∑' y, φ (e a) y := h1`. Use `_ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)`. Introduce `X φ`. Simplify using the standard rewrite rules.

Introduce `α _ h X φ`. Rewrite using `[← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]`. Rewrite using `[← h (X := fun a => X (some a)) (fun a => φ (some a))]`. Rewrite using `[← ENNReal.tsum_mul_right]`. Simplify using `only [Fintype.prod_option]`.

Rewrite using `[ENNReal.tsum_prod']`. Use `congr 1`. Use extensionality with `y`. Rewrite using `[← ENNReal.tsum_mul_left]`. Both sides reduce to the same expression.
-/
theorem tsum_pi_prod_ennreal : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.HL
