import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

/- English proof (translation)
Establish `e : ((r : ℂ) * ((n : ℂ) - r)) / 2 = (1 / 2 : ℂ) * ((r * (n - r) : ℕ) : ℂ)`. Move the coercions through the operations in `[Nat.cast_sub h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.cpow_mul_nat]`. Use `congr 1`.

Rewrite using `[Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]`. Simplify using the standard rewrite rules.
-/
private theorem sqrt_pow (q r n : ℕ) (hq : q ≠ 0) (h : r ≤ n) :
    (((NNReal.sqrt (q : NNReal) : NNReal) : ℝ) : ℂ) ^ (r * (n - r)) =
      (q : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2) := by
  have e : ((r : ℂ) * ((n : ℂ) - r)) / 2 = (1 / 2 : ℂ) * ((r * (n - r) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub h]; ring
  rw [e, Complex.cpow_mul_nat]
  congr 1
  rw [Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

/- English proof (translation)
Introduce `E _ _ n w`. Use `⟨?_, ?_, fun r hr => ?_, fun u hu => ⟨fun i _ => ⟨hu.2 i, fun j hj => hu.1 hj⟩, fun ψ => ?_⟩⟩` and prove the remaining obligations. Establish `hO : Formalism.UG.Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer` using `Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm`. Express the relevant statement in the definitionally equal form `_ = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)`. Rewrite using `[hO]`.

Both sides reduce to the same expression. Conclude with `GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)`. Establish `hq : Spherical.qF (w.adicCompletion E) = Formalism.UG.qV E w`. Unfold `Spherical.qF Formalism.UG.qV`. Rewrite using `[GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Unfold `Spherical.sqrtQ`. Rewrite using `[hq]`. Conclude with `sqrt_pow _ r n (by`. Unfold `Formalism.UG.qV`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `w.ne_bot) hr`. Simplify using `only [Whittaker.psiN, Whittaker.superdiagSum, supN, eq_comm]`.
-/
theorem UpperTheory.V.Af.Smo.sphDict :
    UpperTheory.V.Af.Smo.SphDict := by
  intro E _ _ n w
  refine ⟨?_, ?_, fun r hr => ?_, fun u hu => ⟨fun i _ => ⟨hu.2 i, fun j hj => hu.1 hj⟩, fun ψ => ?_⟩⟩
  · have hO : Formalism.UG.Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
      Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
    change _ = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)
    rw [hO]
    rfl
  · exact GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)
  · have hq : Spherical.qF (w.adicCompletion E) = Formalism.UG.qV E w := by
      unfold Spherical.qF Formalism.UG.qV
      rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Spherical.sqrtQ
    rw [hq]
    exact sqrt_pow _ r n (by
      unfold Formalism.UG.qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot) hr
  · simp only [Whittaker.psiN, Whittaker.superdiagSum, supN, eq_comm]
