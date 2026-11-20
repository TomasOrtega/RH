import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OneOf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DifferentiableSchwartzTranslate
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.HmEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IsRealComp

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D O W Y hY`. Establish `hOne : ∀ t, One F (ex Y t)`. Introduce `t`. Use `oneOf F E D (ex Y t) fun w => ?_` and prove the remaining obligations. Rewrite using `[(exPar E Y).2.2.2.1 hY t]`.

Simplify using the standard rewrite rules. Establish `hL : ∀ (s : ℝ) (ψ : S4 F) (u : V4 F), (W.L (infGL E 2 (ex Y s)) ψ).1 u = ψ.1 (D.act (infGL E 2 (ex Y s))⁻¹ u)`. Introduce `s ψ u`. Establish `h1 : nu F (infGL E 2 (ex Y s)) = 1` using `hOne s`. Rewrite using `[W.L_apply, h1]`.

Establish `h2 : ab (1 : (A F)ˣ) = 1` using `by simp [ab]`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Use `⟨hOne, fun φ t v => ?_⟩` and prove the remaining obligations. Use `set v' : V4 F := D.act (infGL E 2 (ex Y t))⁻¹ v with hv'`.

Take `⟨x, x', hx0, hx, hact, hH⟩` from `vfDer F E D Y v'`. Establish `h0 : HasDerivAt (fun s => φ.1 fun i => v' i + TR.sInf F (x s i)) ((O.dL D Y φ).1 v') 0`. Establish `h` using `sDiff F O φ v' x x' hx0 hx`. Rewrite `h` using `[vfOps F E D O Y hY v' x' hH φ]`. Then use the resulting hypothesis. Establish `hshift : ∀ s, (W.L (infGL E 2 (ex Y (t + s))) φ).1 v = φ.1 fun i => v' i + TR.sInf F (x s i)`.

Introduce `s`. Rewrite using `[(exPar E Y).1 t s, map_mul, map_mul]`. Express the relevant statement in the definitionally equal form `(W.L (infGL E 2 (ex Y t)) (W.L (infGL E 2 (ex Y s)) φ)).1 v = _`. Rewrite using `[hL t, hL s, hact s]`. Establish `h1 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + s))) φ).1 v) ((O.dL D Y φ).1 v') 0`.

Simplify `h0` using `only [hshift]`. Establish `h2 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + (s - t)))) φ).1 v) ((O.dL D Y φ).1 v') t` using `HasDerivAt.comp_sub_const t t (by simpa using h1)`. Rewrite using `[hL t (O.dL D Y φ) v]`. Simplify `h2` using `only [add_sub_cancel]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.dLDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), DLDer O W := by
  intro F E _ _ _ _ _ _ _ D O W Y hY
  have hOne : ∀ t, One F (ex Y t) := by
    intro t
    refine oneOf F E D (ex Y t) fun w => ?_
    rw [(exPar E Y).2.2.2.1 hY t]
    simp
  have hL : ∀ (s : ℝ) (ψ : S4 F) (u : V4 F),
      (W.L (infGL E 2 (ex Y s)) ψ).1 u = ψ.1 (D.act (infGL E 2 (ex Y s))⁻¹ u) := by
    intro s ψ u
    have h1 : nu F (infGL E 2 (ex Y s)) = 1 := hOne s
    rw [W.L_apply, h1]
    have h2 : ab (1 : (A F)ˣ) = 1 := by simp [ab]
    rw [h2]
    simp
  refine ⟨hOne, fun φ t v => ?_⟩
  set v' : V4 F := D.act (infGL E 2 (ex Y t))⁻¹ v with hv'
  obtain ⟨x, x', hx0, hx, hact, hH⟩ := vfDer F E D Y v'
  have h0 : HasDerivAt (fun s => φ.1 fun i => v' i + TR.sInf F (x s i))
      ((O.dL D Y φ).1 v') 0 := by
    have h := sDiff F O φ v' x x' hx0 hx
    rwa [vfOps F E D O Y hY v' x' hH φ] at h
  have hshift : ∀ s, (W.L (infGL E 2 (ex Y (t + s))) φ).1 v =
      φ.1 fun i => v' i + TR.sInf F (x s i) := by
    intro s
    rw [(exPar E Y).1 t s, map_mul, map_mul]
    change (W.L (infGL E 2 (ex Y t)) (W.L (infGL E 2 (ex Y s)) φ)).1 v = _
    rw [hL t, hL s, hact s]
  have h1 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + s))) φ).1 v)
      ((O.dL D Y φ).1 v') 0 := by
    simpa only [hshift] using h0
  have h2 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + (s - t)))) φ).1 v)
      ((O.dL D Y φ).1 v') t :=
    HasDerivAt.comp_sub_const t t (by simpa using h1)
  rw [hL t (O.dL D Y φ) v]
  simpa only [add_sub_cancel] using h2
