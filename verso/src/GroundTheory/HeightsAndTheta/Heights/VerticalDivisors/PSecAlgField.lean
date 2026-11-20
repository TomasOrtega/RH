import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.ComapMaximalIdealParDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecAlgField

/- English proof (translation)
Establish `hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n))` using `IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)`. Establish `h` using `(MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj`. Establish `hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) = genPar k e n`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]`.

Rewrite `h` using `[hc]`. Then use the resulting hypothesis.
-/
theorem genPar_algebraicIndependent (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

end SecAlgField

/- English proof (translation)
Introduce `k _ n e Q g hQ hg`. Use `show IsField (GenSec k e Q)`. Establish `: Module.Finite (GenParField k e n) (GenSec k e Q)` using `h₁ k (GenParField k e n) n e Q g (genPar k e n) (SecAlgField.genPar_algebraicIndependent k e n) hQ hg`. Establish `: IsDomain (GenSec k e Q)` using `h₂ k n e Q g hQ hg`. Conclude with `isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)`.
-/
theorem SecAlgField.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement) :
    SecAlgField.Statement := by
  intro k _ n e Q g hQ hg
  show IsField (GenSec k e Q)
  have : Module.Finite (GenParField k e n) (GenSec k e Q) :=
    h₁ k (GenParField k e n) n e Q g (genPar k e n)
      (SecAlgField.genPar_algebraicIndependent k e n) hQ hg
  have : IsDomain (GenSec k e Q) := h₂ k n e Q g hQ hg
  exact isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)

end

end GroundTheory.Heights₂.Heights.Vertical
