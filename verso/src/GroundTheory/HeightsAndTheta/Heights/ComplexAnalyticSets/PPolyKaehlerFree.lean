import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyKaehlerFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

/- English proof (translation)
Introduce `R k _ _ _ n`. Use `set B := MvPolynomial (Fin n) k`. Establish `hinj : Function.Injective (mapBaseChange R k B)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `(Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx`. Rewrite using `[Subsingleton.elim y 0, map_zero]`. Establish `hex` using `exact_mapBaseChange_map R k B`. Take `⟨l, hl⟩` from `Module.projective_lifting_property ((map R k B B).restrictScalars B) LinearMap.id (map_surjective R k B)`. Set `e` to `((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1`.

Establish `: Module.Free B Ω[B⁄k]` using `Module.Free.of_basis (mvPolynomialBasis k (Fin n))`. Conclude with `Module.Free.of_equiv e.symm`.
-/
theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
