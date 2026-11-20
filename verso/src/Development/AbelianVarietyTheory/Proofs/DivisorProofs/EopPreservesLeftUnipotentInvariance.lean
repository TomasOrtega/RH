import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.UnipInv

/- English proof (translation)
Introduce `E _ _ _ a r f hf τ i j x g`. Establish `hc : chart f.1 (unip x * g) = chart f.1 g`. Use function extensionality and compare the values at `y`. Unfold `chart`. Use `split_ifs`.

Rewrite using `[mul_assoc, hf]`. Both sides reduce to the same expression. Establish `hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g` using `fun X => by`. Simplify using `only [lieD, hc]`. Simplify using `only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]`.
-/
theorem Eop_unip_left :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) →
      ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a),
        (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  intro E _ _ _ a r f hf τ i j x g
  have hc : chart f.1 (unip x * g) = chart f.1 g := by
    funext y
    unfold chart
    split_ifs
    · rw [mul_assoc, hf]
    · rfl
  have hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g := fun X => by
    simp only [lieD, hc]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]

end GlobalTheory.CuspRep.UnipInv
