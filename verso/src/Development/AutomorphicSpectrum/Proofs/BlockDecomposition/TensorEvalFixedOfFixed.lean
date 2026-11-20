import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFix

/- English proof (translation)
Introduce `W C₀ _ _ K₀ _ _ L _ _ k B _ _ ι σB h E hE hW hy v`. Establish `hinj : Function.Injective (ι.comp k)` using `(ι.comp k).injective`. Establish `hg : ∀ x : K₀, σB (ι (k x)) = ι (k x)`. Introduce `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := W) x`.

Establish `hb0 : algebraMap W K₀ b ≠ 0` using `(IsLocalization.map_units K₀ (⟨b, hb⟩ : nonZeroDivisors W)).ne_zero`. Establish `hgb : ι (k (algebraMap W K₀ b)) ≠ 0`. Introduce `h0`. Apply `hb0` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Simplify using `using h0`. Establish `hmul : ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) = ι (k (algebraMap W K₀ a))`. Rewrite using `[← map_mul, ← map_mul, div_mul_cancel₀ _ hb0]`. Apply `mul_right_cancel₀ hgb` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hW b]`. Use `_ = σB (ι (k (algebraMap W K₀ a))) := by rw [← map_mul, hmul]`. Use `_ = ι (k (algebraMap W K₀ a)) := hW a`. Use `_ = ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) := hmul.symm`. Proceed by induction on `v using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => rw [hE, map_mul, hg, hy]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem extension_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  intro W C₀ _ _ K₀ _ _ L _ _ k B _ _ ι σB h E hE hW hy v
  have hinj : Function.Injective (ι.comp k) := (ι.comp k).injective
  have hg : ∀ x : K₀, σB (ι (k x)) = ι (k x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    have hb0 : algebraMap W K₀ b ≠ 0 :=
      (IsLocalization.map_units K₀ (⟨b, hb⟩ : nonZeroDivisors W)).ne_zero
    have hgb : ι (k (algebraMap W K₀ b)) ≠ 0 := by
      intro h0
      apply hb0
      apply hinj
      simpa using h0
    have hmul : ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b))
        = ι (k (algebraMap W K₀ a)) := by
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hb0]
    apply mul_right_cancel₀ hgb
    calc σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * ι (k (algebraMap W K₀ b))
        = σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * σB (ι (k (algebraMap W K₀ b))) := by
          rw [hW b]
      _ = σB (ι (k (algebraMap W K₀ a))) := by rw [← map_mul, hmul]
      _ = ι (k (algebraMap W K₀ a)) := hW a
      _ = ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) := hmul.symm
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hE, map_mul, hg, hy]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end GlobalTheory.CompanionTheory.FrobFix
