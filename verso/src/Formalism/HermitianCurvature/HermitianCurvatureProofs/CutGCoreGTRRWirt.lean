import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

/- English proof (translation)
Establish `hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I` using `(Complex.re_add_im ζ).symm`. Establish `hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Take the linear combination `(-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz + ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq`.
-/
theorem rot_alg (ζ D1 DI : ℂ) : -(ζ.im : ℂ) * D1 + (ζ.re : ℂ) * DI =
    Complex.I * (ζ * ((1 / 2 : ℂ) * (D1 + -Complex.I * DI)) - star ζ * ((1 / 2 : ℂ) * (D1 + Complex.I * DI))) := by
  have hz : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hs : star ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hz +
    ((Complex.I / 2) * D1 + (Complex.I ^ 2 / 2) * DI) * hs + ((ζ.re : ℂ) * DI - (ζ.im : ℂ) * D1) * Complex.I_sq

/- English proof (translation)
Introduce `r u x hu`. Establish `h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I)) (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0` using `((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp`. Establish `h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0`. Establish `h3` using `h1.const_mul x.2`. Simplify using `using h3`.

Establish `hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r)) ((0 : Fin r → ℂ), x.2 * Complex.I) 0` using `by first`. Consider the case `exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2`. Consider the case `exact (hasDerivAt_const (0 : ℝ) x.1).prod h2`. Establish `hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r)` using `by simp`. Establish `hc` using `hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx`.

Establish `hdir1 : MA.dirE (M.vz (r` using `r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]`. Establish `hdir2 : MA.dirE (M.vzb (r` using `r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]`. Establish `hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) + -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I))`. Rewrite using `[MA.wirt, hdir1]`. Simplify using `[M.vz]`.

Establish `hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) + Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I))`. Rewrite using `[MA.wirt, hdir2]`. Simplify using `[M.vzb]`. Establish `key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) = fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I)`. Rewrite using `[hw1, hw2, ← rot_alg]`.

Establish `hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) + (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ))`. Use `Prod.ext (by simp) ?_` and prove the remaining obligations. Simplify using `only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[hv, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `hc`.
-/
theorem rotation_wirtinger_holds : GTRRWirt := by
  intro r u x hu
  have h1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I))
      (Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I) * (1 * Complex.I)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp
  have h2 : HasDerivAt (fun φ : ℝ => x.2 * Complex.exp ((φ : ℂ) * Complex.I)) (x.2 * Complex.I) 0 := by
    have h3 := h1.const_mul x.2
    simpa using h3
  have hγ : HasDerivAt (fun φ : ℝ => ((x.1, x.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E r))
      ((0 : Fin r → ℂ), x.2 * Complex.I) 0 := by
    first
    | exact (hasDerivAt_const (0 : ℝ) x.1).prodMk h2
    | exact (hasDerivAt_const (0 : ℝ) x.1).prod h2
  have hx : x = ((x.1, x.2 * Complex.exp ((((0 : ℝ) : ℂ)) * Complex.I)) : MA.E r) := by simp
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hx
  have hdir1 : MA.dirE (M.vz (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vz]
  have hdir2 : MA.dirE (M.vzb (r := r)) = ((0 : Fin r → ℂ), (1 : ℂ)) := by simp [MA.dirE, M.vzb]
  have hw1 : MA.wirt M.vz u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      -Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir1]
    simp [M.vz]
  have hw2 : MA.wirt M.vzb u x = (1 / 2 : ℂ) * (fderiv ℝ u x ((0 : Fin r → ℂ), (1 : ℂ)) +
      Complex.I * fderiv ℝ u x ((0 : Fin r → ℂ), Complex.I)) := by
    rw [MA.wirt, hdir2]
    simp [M.vzb]
  have key : Complex.I * (x.2 * MA.wirt M.vz u x - star x.2 * MA.wirt M.vzb u x) =
      fderiv ℝ u x ((0 : Fin r → ℂ), x.2 * Complex.I) := by
    rw [hw1, hw2, ← rot_alg]
    have hv : ((0 : Fin r → ℂ), x.2 * Complex.I) = x.2.re • ((0 : Fin r → ℂ), Complex.I) +
        (-x.2.im) • ((0 : Fin r → ℂ), (1 : ℂ)) := by
      refine Prod.ext (by simp) ?_
      simp only [Prod.smul_snd, Prod.snd_add, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp
    rw [hv, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [key]
  exact hc

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
