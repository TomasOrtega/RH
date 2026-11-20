import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.PiInfInclR
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ContinuousMhUInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
The claim follows from `(Module.finBasis ℚ E).equivFun.injective.countable`.
-/
theorem countable_E : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable

/- English proof (translation)
Use `haveI := countable_E (E := E)`. Conclude with `inferInstanceAs (Countable (Fin p → Fin q → E))`.
-/
theorem countable_mat (p q : ℕ) : Countable (Matrix (Fin p) (Fin q) E) := by
  haveI := countable_E (E := E)
  exact inferInstanceAs (Countable (Fin p → Fin q → E))

def tr (d : SD σ) (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E) : Mx F E d.m d.n := mat g⁻¹ * incM F X

/- English proof (translation)
Establish `h1 : Continuous (f ∘ d.cmb)` using `PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf`. Establish `e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y)` using `fun Y => by simp [Kdil.Tb.cmb_crd]`. Establish `h2 : Continuous fun h : UA σ d.A.J => (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E))` using `Units.continuous_coe_inv.comp continuous_subtype_val`. Simplify using `only [tr, e, Kdil.Tb.crd_mul]`. Conclude with `h1.comp (((Kdil.Tb.continuous_mh d).comp h2).matrix_mulVec continuous_const)`.
-/
theorem cont_tr (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    Continuous fun g : UA σ d.A.J => f (tr d g X) := by
  have h1 : Continuous (f ∘ d.cmb) := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [Kdil.Tb.cmb_crd]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [tr, e, Kdil.Tb.crd_mul]
  exact h1.comp (((Kdil.Tb.continuous_mh d).comp h2).matrix_mulVec continuous_const)

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`. Simplify using `only [SD.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add, map_smul, smul_eq_mul, Matrix.trace_mul_comm G β]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chr_comb (d : SD σ) (β G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [SD.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add, map_smul, smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring

/- English proof (translation)
Establish `h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1`. Rewrite using `[← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `i j`.

Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite `this` using `[Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def]`. Rewrite using `[Matrix.smul_apply, zsmul_eq_mul]`. Use `push_cast`. Take the linear combination `2 * this - G i j * h2`.

Introduce and unpack `rfl`. Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]`. Use `push_cast`. Take the linear combination `(-T i j) * h2`.
-/
theorem half_eq_iff (d : SD σ) (G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2

end PositivityTheory.SiegelWeilFormula.Tauto

end
