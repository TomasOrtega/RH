import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NegIndexTransposeOfHasSignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.EmbChange

open scoped Matrix
open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)` after adjusting the coercions. Establish `h2 : D.host.sqrtMinusD ≠ 0`. Introduce `h`. Use `D.host.sqrtMinusD_sq` as an intermediate fact.

Rewrite `this` using `[h]`. Establish `hd : (D.host.d : D.host.E) ≠ 0`. Use `D.host.qd_big.2` as an intermediate fact. Conclude with `(by omega : D.host.d ≠ 0)` after adjusting the coercions. Apply `hd` to reduce the goal to its premises.

Take the linear combination `this`. Unfold `Formalism.BasicNotions.Host.xi0`. Conclude with `div_ne_zero (by norm_num) (mul_ne_zero h1 h2)`.
-/
theorem embedding_xi_zero_ne_zero (D : D7) : D.host.xi0 ≠ 0 := by
  have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
  have h2 : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have := D.host.sqrtMinusD_sq
    rw [h] at this
    have hd : (D.host.d : D.host.E) ≠ 0 := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : D.host.d ≠ 0)
    apply hd
    linear_combination this
  unfold Formalism.BasicNotions.Host.xi0
  exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)

end GlobalTheory.EmbChange
