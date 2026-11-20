import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

open MeasureTheory Polynomial

namespace GlobalTheory.CompanionTheory.TfLoc

open PositivityTheory.Rg.Tf.Loc

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simpa using hp.add_right hq`. Consider the case `monomial m a`. Rewrite using `[aeval_monomial]`. Conclude with `(Algebra.commute_algebraMap_right a A).mul_right (hc.pow_right m)`.
-/
theorem commute_aeval_right {K : Type*} [Field K] {n : ℕ} {A M : Matrix (Fin n) (Fin n) K}
    (hc : Commute A M) (p : K[X]) : Commute A (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a A).mul_right (hc.pow_right m)

/- English proof (translation)
Introduce `hD _ hA`. Unfold `D0a at hD`. Unfold `A1 at hA`. Unfold `MeasureTransportOpenSet`. Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n _ _ _ _ SE Sk hSE hSk δ γ h μδ μγ hreg hN hmap y z hz`.

Establish `hinc : Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E))` using `(hD k E hur σ hgen).2.2.2.2.2 n`. Establish `hcf : Continuous (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h)` using `(continuous_const.mul continuous_subtype_val).mul continuous_const`. Establish `hci : Continuous (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k))` using `hinc.comp continuous_subtype_val`. Establish `hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable`. Establish `h0` using `hreg`.

Unfold `IsTwRegSemisimple at h0`. Rewrite `h0` using `[hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`. Conclude with `h0`. Take `⟨p, hp⟩` from `hA E n _ hsep (z : Matrix (Fin n) (Fin n) E) hz`. Establish `hzt : ∀ t : Subgroup.centralizer {γ}, z * incl (t : GL (Fin n) k) = incl (t : GL (Fin n) k) * z`.

Introduce `t`. Establish `ht : (t : GL (Fin n) k) * γ = γ * t` using `Subgroup.mem_centralizer_singleton_iff.mp t.2`. Establish `hc : Commute ((incl (t : GL (Fin n) k) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)`. Use `congrArg (fun g => ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) ht` as an intermediate fact. Simplify `this` using `[Commute, SemiconjBy, map_mul, Units.val_mul]`.

Establish `hc2` using `commute_aeval_right hc p`. Rewrite `hc2` using `[← hp]`. Conclude with `Units.ext hc2.symm.eq`. Use `set S' : Set (GL (Fin n) E) := {w | (z * incl y)⁻¹ * w * (z * incl y) ∈ SE} with hS'`. Establish `hopen : IsOpen S'` using `hSE.preimage ((continuous_const.mul continuous_id).mul continuous_const)`.

Establish `hmeas : MeasurableSet S'` using `hopen.measurableSet`. Establish `e1 : μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} = Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ S'`. Rewrite using `[Measure.map_apply hcf.measurable hmeas]`. Use `congr 1`. Use extensionality with `x`.

Establish `: (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) = (z * incl y)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h) * (z * incl y)` using `by group`. Simplify using `only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this]`. Establish `e2 : Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ S' = μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk}`. Rewrite using `[Measure.map_apply hci.measurable hmeas]`. Use `congr 1`.

Use extensionality with `t`. Establish `: (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y) = incl (y⁻¹ * (t : GL (Fin n) k) * y)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this, hSk]`. Rewrite using `[e1, hmap, e2]`.
-/
theorem transport_open_trace : D0a → T0 → A1 → MeasureTransportOpenSet := by
  intro hD _ hA
  unfold D0a at hD
  unfold A1 at hA
  unfold MeasureTransportOpenSet
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n _ _ _ _ SE Sk hSE hSk δ γ h μδ μγ hreg hN hmap y z hz
  have hinc : Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E)) :=
    (hD k E hur σ hgen).2.2.2.2.2 n
  have hcf : Continuous (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hci : Continuous (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) :=
    hinc.comp continuous_subtype_val

  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have h0 := hreg
    unfold IsTwRegSemisimple at h0
    rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at h0
    exact h0
  obtain ⟨p, hp⟩ := hA E n _ hsep (z : Matrix (Fin n) (Fin n) E) hz

  have hzt : ∀ t : Subgroup.centralizer {γ},
      z * incl (t : GL (Fin n) k) = incl (t : GL (Fin n) k) * z := by
    intro t
    have ht : (t : GL (Fin n) k) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.mp t.2
    have hc : Commute ((incl (t : GL (Fin n) k) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
      have := congrArg (fun g => ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) ht
      simpa [Commute, SemiconjBy, map_mul, Units.val_mul] using this
    have hc2 := commute_aeval_right hc p
    rw [← hp] at hc2
    exact Units.ext hc2.symm.eq
  set S' : Set (GL (Fin n) E) := {w | (z * incl y)⁻¹ * w * (z * incl y) ∈ SE} with hS'
  have hopen : IsOpen S' :=
    hSE.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hmeas : MeasurableSet S' := hopen.measurableSet
  have e1 : μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} =
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ S' := by
    rw [Measure.map_apply hcf.measurable hmeas]
    congr 1
    ext x
    have : (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) =
        (z * incl y)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h) * (z * incl y) := by group
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this]
  have e2 : Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ S' =
      μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk} := by
    rw [Measure.map_apply hci.measurable hmeas]
    congr 1
    ext t
    have : (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y) =
        incl (y⁻¹ * (t : GL (Fin n) k) * y) := by
      calc (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y)
          = (incl y)⁻¹ * (z⁻¹ * (incl (t : GL (Fin n) k) * z)) * incl y := by group
        _ = (incl y)⁻¹ * (z⁻¹ * (z * incl (t : GL (Fin n) k))) * incl y := by rw [hzt t]
        _ = (incl y)⁻¹ * incl (t : GL (Fin n) k) * incl y := by group
        _ = incl (y⁻¹ * (t : GL (Fin n) k) * y) := by simp only [map_mul, map_inv]
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this, hSk]
  rw [e1, hmap, e2]

end GlobalTheory.CompanionTheory.TfLoc
