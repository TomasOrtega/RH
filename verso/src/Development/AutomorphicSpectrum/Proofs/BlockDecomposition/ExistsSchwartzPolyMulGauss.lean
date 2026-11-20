import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz

variable {m n : ℕ}

def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

/- English proof (translation)
Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data. A detailed English derivation is pending.
-/
theorem coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)

def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid m n)
    (GroundTheory.Global.gaussianSchwartz (PiLp 2 (fun _ : Fin m × Fin n => ℂ))), fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_toEuclid_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem exists_schwartz_poly_mul_gauss (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
        Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := exists_gauss (m := m) (n := n)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => coord k u) P) g, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (eval_temperate P), hg, smul_eq_mul]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem main : ∀ (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ), ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
    ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
      Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) :=
  exists_schwartz_poly_mul_gauss

end GlobalTheory.CompanionTheory.PolyGaussSchwartz
