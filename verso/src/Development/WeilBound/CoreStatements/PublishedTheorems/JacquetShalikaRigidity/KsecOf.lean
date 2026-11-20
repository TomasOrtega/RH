import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

/- English proof (translation)
Introduce `hG2c hG5 hG1d hK9 E _ _ _ k hk ψ hψ hcof π hπ`. Take `⟨S₀, hS₀⟩` from `hK9 E k hk ψ hψ hcof π hπ`. Use `⟨S₀, fun S hS => ⟨(hS₀ S hS).1, fun α hα => ?_⟩⟩` and prove the remaining obligations. Take `⟨φ, hφ, h, x, hh, hx, hsat, -, hone⟩` from `(hS₀ S hS).2 α hα`. Establish `hval : ∀ g, Rt E k h x g = φ.1 (g * h)` using `fun g => by rw [Rt_apply, hx]`.

Establish `hgood : Good ψ (k - 1) (x : GA E k → ℂ)`. Rewrite using `[hx]`. Conclude with `good_of_isCuspForm E k ψ φ (π.cusp φ hφ)`. Use `⟨φ, hφ, h, Rt E k h x, hval, ?_⟩` and prove the remaining obligations. Use `⟨(hG5 E k ψ hψ).2.2.1 x h hgood, ?_, ?_, ?_, ?_, ?_, hone⟩` and prove the remaining obligations.

Introduce `γ g`. Rewrite using `[hval, hval, mul_assoc]`. Conclude with `(π.cusp φ hφ).1.left γ (g * h)`. Introduce `t g`. Rewrite using `[hval, hval, mul_assoc]`.

Conclude with `hπ φ hφ t (g * h)`. Introduce `w`. Take `⟨Y, -, hYst, hYmem⟩` from `hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)`. Conclude with `(hYmem _).1 (hYst h (hh w.1 w.2) x ((hYmem x).2 (hsat w)))`. Establish `e : (⇑(Rt E k h x) : GA E k → ℂ) = fun g => φ.1 (g * h)` using `funext hval`.

Rewrite using `[e]`. Conclude with `(hG1d E k hk π hπ φ hφ h).1`. Use `(hG1d E k hk π hπ φ hφ h).2` as an intermediate fact. Simplify `this` using `only [hval]`.
-/
theorem ksec_of : jumpWindows.G2c → jumpWindows.G5 → CuspDecayShortRowColumn → K9 → KSec := by
  intro hG2c hG5 hG1d hK9 E _ _ _ k hk ψ hψ hcof π hπ
  obtain ⟨S₀, hS₀⟩ := hK9 E k hk ψ hψ hcof π hπ
  refine ⟨S₀, fun S hS => ⟨(hS₀ S hS).1, fun α hα => ?_⟩⟩
  obtain ⟨φ, hφ, h, x, hh, hx, hsat, -, hone⟩ := (hS₀ S hS).2 α hα
  have hval : ∀ g, Rt E k h x g = φ.1 (g * h) := fun g => by rw [Rt_apply, hx]
  have hgood : Good ψ (k - 1) (x : GA E k → ℂ) := by
    rw [hx]; exact good_of_isCuspForm E k ψ φ (π.cusp φ hφ)
  refine ⟨φ, hφ, h, Rt E k h x, hval, ?_⟩
  refine ⟨(hG5 E k ψ hψ).2.2.1 x h hgood, ?_, ?_, ?_, ?_, ?_, hone⟩
  · intro γ g
    rw [hval, hval, mul_assoc]
    exact (π.cusp φ hφ).1.left γ (g * h)
  · intro t g
    rw [hval, hval, mul_assoc]
    exact hπ φ hφ t (g * h)
  · intro w
    obtain ⟨Y, -, hYst, hYmem⟩ := hG2c E k w.1 (Finset.univ.val.map (α w)) (by simp)
    exact (hYmem _).1 (hYst h (hh w.1 w.2) x ((hYmem x).2 (hsat w)))
  · have e : (⇑(Rt E k h x) : GA E k → ℂ) = fun g => φ.1 (g * h) := funext hval
    rw [e]
    exact (hG1d E k hk π hπ φ hφ h).1
  · have := (hG1d E k hk π hπ φ hφ h).2
    simpa only [hval] using this

end PositivityTheory.AdelicQuotientData

end
