import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Glob

/- English proof (translation)
Introduce `s x y hs hx hy`. Establish `key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z`. Introduce `z hz`. Establish `h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum`. Rewrite using `[Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']`.

Simplify using `[nsmul_eq_mul]`. Establish `h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum` using `by conv_lhs => rw [hz]`. Conclude with `h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : (Multiset.card s : ℤ) ≠ 0`.

Conclude with `(mt Multiset.card_eq_zero.mp hs)` after adjusting the coercions. Use `(key x hx).symm.trans (key y hy)` as an intermediate fact. Conclude with `mul_left_cancel₀ hc this`.
-/
theorem symm_multiset_centre_unique : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  intro s x y hs hx hy
  have key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z := by
    intro z hz
    have h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum := by
      rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']
      simp [nsmul_eq_mul]
    have h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum := by
      conv_lhs => rw [hz]
      exact h1
    linarith
  have hc : (Multiset.card s : ℤ) ≠ 0 := by
    exact_mod_cast (mt Multiset.card_eq_zero.mp hs)
  have := (key x hx).symm.trans (key y hy)
  exact mul_left_cancel₀ hc this

end GlobalTheory.Glob
