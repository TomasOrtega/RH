import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.SiegelWeilFormula.KMain

open PositivityTheory.Rg.Sw

def coordX {m n : ℕ} (k : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Split into cases according to the possible forms of the given data. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem coordX_temperate {m n : ℕ} (k : Fin m × Fin n × Bool) : Function.HasTemperateGrowth (coordX k) := by
  rcases k with ⟨a, i, β⟩
  cases β
  · have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)).hasTemperateGrowth
    convert h using 1
    funext x
    simp [coordX]
  · have h := ((Complex.conjCLE.toContinuousLinearMap).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a))).hasTemperateGrowth
    convert h using 1
    funext x
    simp [coordX]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem evX_temperate {m n : ℕ} (P : PX m n) : Function.HasTemperateGrowth (fun x => evX P x) := by
  have hev : (fun x => evX P x) = fun x => MvPolynomial.eval (fun k => coordX k x) P := by
    funext x
    rfl
  rw [hev]
  induction P using MvPolynomial.induction_on with
  | C c0 =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const c0
  | add p q hp hq =>
    simp only [map_add]
    exact Function.HasTemperateGrowth.add (hp rfl) (hq rfl)
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact Function.HasTemperateGrowth.mul (hp rfl) (coordX_temperate k)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis.

Apply the first step, then apply the next step to every resulting obligation. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Apply the first step, then apply the next step to every resulting obligation. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation. By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem schwartz_gs {m n : ℕ} (c : ℝ) (hc : 0 < c) : ∃ φ : 𝓢(Fin m → Fin n → ℂ, ℂ), ⇑φ = gs c := by
  have hs : 0 < Real.sqrt (c / Real.pi) := Real.sqrt_pos.mpr (div_pos hc Real.pi_pos)
  have hs2 : Real.sqrt (c / Real.pi) ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let L : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin n × Bool) :=
    { toFun := fun x => WithLp.toLp 2 (fun p => Real.sqrt (c / Real.pi) *
        (if p.2.2 then (x p.1 p.2.1).im else (x p.1 p.2.1).re))
      invFun := fun y => fun a i => ⟨(Real.sqrt (c / Real.pi))⁻¹ * y (a, i, false),
        (Real.sqrt (c / Real.pi))⁻¹ * y (a, i, true)⟩
      map_add' := fun x y => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp <;> ring
      map_smul' := fun r x => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp <;> ring
      left_inv := fun x => by
        funext a i
        apply Complex.ext <;> simp [hs.ne']
      right_inv := fun y => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp [hs.ne'] }
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.toContinuousLinearEquiv
    (GroundTheory.Global.gaussianSchwartz _), ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  funext x
  simp only [Function.comp_apply, GroundTheory.Global.gaussianSchwartz_apply, gs]
  rw [Complex.ofReal_exp]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [L, Fintype.sum_prod_type, Fintype.sum_bool, mul_pow, hs2, Complex.sq_norm, Complex.normSq_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem schwartz_polyGauss {m n : ℕ} (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : 𝓢(Fin m → Fin n → ℂ, ℂ), ⇑φ = fun x => evX P x * gs c x := by
  obtain ⟨g, hg⟩ := schwartz_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => evX P x) g, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P), hg]
  rfl

end PositivityTheory.SiegelWeilFormula.KMain

end
