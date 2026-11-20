import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal mConeMap)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace AddBlockEq

def toIndefiniteRowSideFullHecke {P : ArithVariety n} (D : GroundTheory.Heights₂.Heights.AddBlockData P) : AddBlockData P where
  deg := D.deg
  m := D.size
  x j := funFieldEquiv P (D.elt j)
  homog j := (isOfDegree_iff P D.deg (D.elt j)).1 (D.elt_deg j)
  chart c hc j := by
    have h := (funFieldEquiv_mem_chartRing_iff P c _).2 (D.chart_mem c hc j)
    rwa [map_div₀, funFieldEquiv_chartPow, div_eq_mul_inv, ← chartPow_neg] at h
  unit c hc := by
    obtain ⟨u, hu, hsum⟩ := D.generating c hc
    refine ⟨fun j ↦ funFieldEquiv P (u j), fun j ↦ (funFieldEquiv_mem_chartRing_iff P c _).2 (hu j), ?_⟩
    have h := congrArg (funFieldEquiv P) hsum
    simpa only [map_sum, map_mul, map_div₀, map_inv₀, map_one, funFieldEquiv_chartPow, div_eq_mul_inv,
      chartPow_neg] using h

def split_model_to_place_model {P : ArithVariety n} (D : AddBlockData P) : GroundTheory.Heights₂.Heights.AddBlockData P where
  deg := D.deg
  size := D.m
  elt j := (funFieldEquiv P).symm (D.x j)
  elt_deg j := by
    rw [isOfDegree_iff, RingEquiv.apply_symm_apply]
    exact D.homog j
  chart_mem c hc j := by
    rw [← funFieldEquiv_mem_chartRing_iff, map_div₀, funFieldEquiv_chartPow, RingEquiv.apply_symm_apply,
      div_eq_mul_inv, ← chartPow_neg]
    exact D.chart c hc j
  generating c hc := by
    obtain ⟨u, hu, hsum⟩ := D.unit c hc
    refine ⟨fun j ↦ (funFieldEquiv P).symm (u j), fun j ↦ ?_, ?_⟩
    · rw [← funFieldEquiv_mem_chartRing_iff, RingEquiv.apply_symm_apply]
      exact hu j
    · apply (funFieldEquiv P).injective
      simpa only [map_sum, map_mul, map_div₀, map_inv₀, map_one, funFieldEquiv_chartPow, div_eq_mul_inv,
        chartPow_neg, RingEquiv.apply_symm_apply] using hsum

def addBlockEquiv (P : ArithVariety n) :
    GroundTheory.Heights₂.Heights.AddBlockData P ≃ AddBlockData P where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv D := by
    cases D
    simp only [toIndefiniteRowSideFullHecke, split_model_to_place_model, RingEquiv.symm_apply_apply]
  right_inv D := by
    cases D
    simp only [toIndefiniteRowSideFullHecke, split_model_to_place_model, RingEquiv.apply_symm_apply]

section Ext

variable {P : ArithVariety n} (D : GroundTheory.Heights₂.Heights.AddBlockData P)

/- English proof (translation)
Break down `v with ⟨_ | k, i⟩` into its components or cases. Both sides reduce to the same expression. Conclude with `(funFieldEquiv_mkF P _).symm`.
-/
theorem addBlockEquiv_genericPoint (v : Coord D.extSizes) : (toIndefiniteRowSideFullHecke D).yPlus v = funFieldEquiv P (D.extVal v) := by
  rcases v with ⟨_ | k, i⟩
  · rfl
  · exact (funFieldEquiv_mkF P _).symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `aeval (fun p : Coord D.extSizes ↦ C ((toIndefiniteRowSideFullHecke D).yPlus p) * X p.1) f = _`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => simp [GroundTheory.Heights₂.Heights.AddBlockData.extMap]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p v hp`.

Rewrite using `[map_mul, map_mul, map_mul, hp]`. Simplify using `[GroundTheory.Heights₂.Heights.AddBlockData.extMap, addBlockEquiv_genericPoint]`.
-/
theorem coneMap_addBlockEquiv (f : MvPolynomial (Coord D.extSizes) ℤ) :
    mConeMap (toIndefiniteRowSideFullHecke D).yPlus f =
      MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P) (D.extMap f) := by
  change aeval (fun p : Coord D.extSizes ↦ C ((toIndefiniteRowSideFullHecke D).yPlus p) * X p.1) f = _
  induction f using MvPolynomial.induction_on with
  | C r => simp [GroundTheory.Heights₂.Heights.AddBlockData.extMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [GroundTheory.Heights₂.Heights.AddBlockData.extMap, addBlockEquiv_genericPoint]

/- English proof (translation)
Use extensionality with `f`. Establish `h` using `coneMap_addBlockEquiv D f`. Express the relevant statement in the definitionally equal form `mConeMap (toIndefiniteRowSideFullHecke D).yPlus f = 0 ↔ D.extMap f = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Conclude with `MvPolynomial.map_injective _ (funFieldEquiv P).injective ((h.symm.trans h0).trans (map_zero _).symm)`. Introduce `h0`. Conclude with `h.trans (by rw [h0, map_zero])`.
-/
theorem addBlockEquiv_extIdeal : (toIndefiniteRowSideFullHecke D).ext = D.extIdeal := by
  ext f
  have h := coneMap_addBlockEquiv D f
  change mConeMap (toIndefiniteRowSideFullHecke D).yPlus f = 0 ↔ D.extMap f = 0
  constructor
  · intro h0
    exact MvPolynomial.map_injective _ (funFieldEquiv P).injective
      ((h.symm.trans h0).trans (map_zero _).symm)
  · intro h0
    exact h.trans (by rw [h0, map_zero])

/- English proof (translation)
Rewrite using `[addBlockEquiv_extIdeal]`. Both sides reduce to the same expression.
-/
theorem extPoints_eq : D.extPoints = conePoints (toIndefiniteRowSideFullHecke D).ext ℂ := by
  rw [addBlockEquiv_extIdeal]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `o`. Apply the tactic sequence `cases o <;> rfl`.
-/
theorem addBlockEquiv_join {F : Type*} (z : Cone n F) (z' : Fin (D.size + 1) → F) :
    (toIndefiniteRowSideFullHecke D).join z z' = D.joinPt z z' := by
  funext o
  cases o <;> rfl

end Ext

section OfTwin

variable {P : ArithVariety n} (D : AddBlockData P)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with ⟨_ | k, i⟩` into its components or cases. Conclude with `RingEquiv.apply_symm_apply _ _`. Both sides reduce to the same expression.
-/
theorem addBlockEquiv_symm_genericPoint : (toIndefiniteRowSideFullHecke (split_model_to_place_model D)).yPlus = D.yPlus := by
  funext v
  rcases v with ⟨_ | k, i⟩
  · exact RingEquiv.apply_symm_apply _ _
  · rfl

/- English proof (translation)
The claim follows from `(addBlockEquiv_extIdeal (split_model_to_place_model D)).symm.trans (congrArg mCoordIdeal (addBlockEquiv_symm_genericPoint D))`.
-/
theorem addBlockEquiv_symm_extIdeal : (split_model_to_place_model D).extIdeal = D.ext :=
  (addBlockEquiv_extIdeal (split_model_to_place_model D)).symm.trans (congrArg mCoordIdeal (addBlockEquiv_symm_genericPoint D))

/- English proof (translation)
Rewrite using `[extPoints_eq, addBlockEquiv_extIdeal, addBlockEquiv_symm_extIdeal]`. Both sides reduce to the same expression.
-/
theorem addBlockEquiv_symm_conePoints : (split_model_to_place_model D).extPoints = conePoints D.ext ℂ := by
  rw [extPoints_eq, addBlockEquiv_extIdeal, addBlockEquiv_symm_extIdeal]
  rfl

end OfTwin

end AddBlockEq

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
