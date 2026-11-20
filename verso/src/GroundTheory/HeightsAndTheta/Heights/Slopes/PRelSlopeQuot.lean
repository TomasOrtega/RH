import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Slopes
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PChainSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace HermitianBundle

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Rewrite using `[normDegree, deg, degree_eq_arithDegree]`. Both sides reduce to the same expression.
-/
theorem normDegree_eq_deg_sub (E : HermitianBundle K) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F = (E.sub F).deg := by
  rw [normDegree, deg, degree_eq_arithDegree]
  rfl

end HermitianBundle

/- English proof (translation)
Introduce `K _ _ E F G hF hFG`. Use `set F' := F.comap G.subtype`. Use `set hF' := hF.comap_subtype G`. Use `set X := HermitianBundle.subQuotExtension (E.sub G) F' hF'`. Establish `hdeg : (E.sub G).deg = ((E.sub G).sub F').deg + ((E.sub G).quot F' hF').deg`.

Simplify using `only [HermitianBundle.deg]`. Rewrite using `[X.arithDegree_eq_add, add_div]`. Establish `hsubF : ((E.sub G).sub F').deg = (E.sub F).deg` using `LatticeLemmas.ChainSum.deg_sub_comap E hFG.le`. Establish `hrk` using `X.finrank_eq`. Establish `hrkF : Module.finrank (𝓞 K) ((E.sub G).sub F').carrier = Module.finrank (𝓞 K) F` using `(Submodule.comapSubtypeEquivOfLe hFG.le).finrank_eq`.

Establish `hrk' : (E.rank G : ℝ) - E.rank F = Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier`. Establish `h : E.rank G = E.rank F + Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier`. Rewrite using `[HermitianBundle.rank, HermitianBundle.rank, ← hrkF]`. Conclude with `hrk`. Rewrite using `[h, Nat.cast_add, add_sub_cancel_left]`.

Rewrite using `[HermitianBundle.relSlope, hrk', HermitianBundle.normDegree_eq_deg_sub, HermitianBundle.normDegree_eq_deg_sub, hdeg, hsubF, add_sub_cancel_left, HermitianBundle.bundleSlope]`. Both sides reduce to the same expression.
-/
theorem RelSlopeQuot.proof : RelSlopeQuot.Statement := by
  intro K _ _ E F G hF hFG
  set F' := F.comap G.subtype
  set hF' := hF.comap_subtype G
  set X := HermitianBundle.subQuotExtension (E.sub G) F' hF'
  have hdeg : (E.sub G).deg = ((E.sub G).sub F').deg + ((E.sub G).quot F' hF').deg := by
    simp only [HermitianBundle.deg]
    rw [X.arithDegree_eq_add, add_div]
  have hsubF : ((E.sub G).sub F').deg = (E.sub F).deg :=
    LatticeLemmas.ChainSum.deg_sub_comap E hFG.le
  have hrk := X.finrank_eq
  have hrkF : Module.finrank (𝓞 K) ((E.sub G).sub F').carrier = Module.finrank (𝓞 K) F :=
    (Submodule.comapSubtypeEquivOfLe hFG.le).finrank_eq
  have hrk' : (E.rank G : ℝ) - E.rank F =
      Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier := by
    have h : E.rank G = E.rank F + Module.finrank (𝓞 K) ((E.sub G).quot F' hF').carrier := by
      rw [HermitianBundle.rank, HermitianBundle.rank, ← hrkF]
      exact hrk
    rw [h, Nat.cast_add, add_sub_cancel_left]
  rw [HermitianBundle.relSlope, hrk', HermitianBundle.normDegree_eq_deg_sub,
    HermitianBundle.normDegree_eq_deg_sub, hdeg, hsubF, add_sub_cancel_left,
    HermitianBundle.bundleSlope]
  rfl

end

end GroundTheory.Heights₂.Heights
