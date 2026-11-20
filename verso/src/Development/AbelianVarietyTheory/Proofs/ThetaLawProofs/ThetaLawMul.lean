import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi in

/- English proof (translation)
Introduce `g x y n n' m m' k k' hx hy Hy Hx`. Take `⟨c₁, hc₁, h₁⟩` from `Hy`. Take `⟨c₂, hc₂, h₂⟩` from `Hx`. Use `⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩` and prove the remaining obligations. Establish `hjy` using `jAut_isUnit hy hτ`.

Establish `hτ₂` using `spAct_mem hy hτ`. Establish `hjx` using `jAut_isUnit hx hτ₂`. Rewrite using `[spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy, expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaLaw_mul : ∀ (g : ℕ) (sp sq : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (n n' m m' k k' : Fin g → ℤ), sp ∈ Matrix.symplecticGroup (Fin g) ℤ → sq ∈ Matrix.symplecticGroup (Fin g) ℤ → GlobalTheory.KeyPow.ThetaLaw g sq n n' m m' → GlobalTheory.KeyPow.ThetaLaw g sp m m' k k' → GlobalTheory.KeyPow.ThetaLaw g (sp * sq) n n' k k' := by
  intro g x y n n' m m' k k' hx hy Hy Hx
  obtain ⟨c₁, hc₁, h₁⟩ := Hy
  obtain ⟨c₂, hc₂, h₂⟩ := Hx
  refine ⟨c₂ * c₁, by rw [mul_pow, hc₁, hc₂, _root_.one_mul], fun τ hτ z => ?_⟩
  have hjy := jAut_isUnit hy hτ
  have hτ₂ := spAct_mem hy hτ
  have hjx := jAut_isUnit hx hτ₂
  rw [spAct_mul x y τ hjy, zAct_mul x y τ hjy z, h₂ _ hτ₂, h₁ τ hτ z, det_jAut_mul x y τ hjy,
    expArg_mul x y τ hjy hjx (sp_A hy hτ.1 hjy) z, eC_add]
  ring

end GlobalTheory.KeyPow
