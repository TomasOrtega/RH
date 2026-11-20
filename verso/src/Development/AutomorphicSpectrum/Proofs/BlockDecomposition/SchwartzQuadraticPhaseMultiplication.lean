import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open scoped Matrix SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.QuadChirp

/- English proof (translation)
Establish `h : (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = Matrix.trace (b * (Aᴴ * A))`. Rewrite using `[show (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = star (Matrix.trace (b * (Aᴴ * A))) from rfl, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.trace_mul_comm]`. Conclude with `Complex.conj_eq_iff_re.1 h`.
-/
theorem ofReal_re_trace {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (b * (Aᴴ * A))).re : ℝ) : ℂ) = Matrix.trace (b * (Aᴴ * A)) := by
  have h : (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = Matrix.trace (b * (Aᴴ * A)) := by
    rw [show (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = star (Matrix.trace (b * (Aᴴ * A))) from rfl,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

/- English proof (translation)
The claim follows from `((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth`.
-/
theorem coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u l i) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

/- English proof (translation)
The claim follows from `((Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth`.
-/
theorem conj_coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) :=
  ((Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

/- English proof (translation)
Establish `heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) = fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i)`. Use function extensionality and compare the values at `u`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[heq]`. Use `Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ => Function.HasTemperateGrowth.sum fun l _ => ?_` and prove the remaining obligations.

Conclude with `(Function.HasTemperateGrowth.const (b i j)).mul ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))`.
-/
theorem trace_hasTemperateGrowth {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) := by
  have heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) =
      fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i) := by
    funext u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
  rw [heq]
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  exact (Function.HasTemperateGrowth.const (b i j)).mul
    ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))

/- English proof (translation)
Establish `hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re)` using `(Function.HasTemperateGrowth.const k).mul (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))`. Establish `hcomp` using `GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre`. Use `hcomp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Rewrite using `[Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]`.

Use `congr 1`. Establish `hT` using `GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)`. Rewrite using `[Complex.ofReal_mul]`. Use `conv_lhs => rw [← hT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chirp_hasTemperateGrowth {m n : ℕ} (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) := by
  have hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re) :=
    (Function.HasTemperateGrowth.const k).mul
      (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))
  have hcomp := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre
  convert hcomp using 1
  funext u
  rw [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
  congr 1
  have hT := GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)
  rw [Complex.ofReal_mul]
  conv_lhs => rw [← hT]
  ring

/- English proof (translation)
Introduce `m n k b hb φ`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]`.
-/
theorem exists_schwartz_chirp_mul :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  intro m n k b hb φ
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi *
    Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]

end GlobalTheory.CompanionTheory.QuadChirp
