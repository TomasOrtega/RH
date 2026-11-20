import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.EvGel

section Dual

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def dualFam (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualFam_apply (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    dualFam E a b φ v = φ (E b a v) := rfl

/- English proof (translation)
Introduce `a b c d`. Use `LinearMap.ext fun φ => LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `h2` using `congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]`.

Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h3 : d = a`. Substitute `h1` using the available equality. Substitute `h3` using the available equality. Simplify `h2` using `[dualFam_apply]`. Substitute `h1` using the available equality.

Simplify `h2` using `[dualFam_apply, h3, Ne.symm h3]`. Substitute `h3` using the available equality. Simplify `h2` using `[dualFam_apply, h1, Ne.symm h1]`. Simplify `h2` using `[dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3]`.
-/
theorem glRel_dualFam {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (dualFam E) := by
  intro a b c d
  refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
  have h2 := congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simpa [dualFam_apply] using h2
  · subst h1; simpa [dualFam_apply, h3, Ne.symm h3] using h2
  · subst h3; simpa [dualFam_apply, h1, Ne.symm h1] using h2
  · simpa [dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3] using h2

/- English proof (translation)
Proceed by induction on `m generalizing a b φ v with`. Consider the case `zero`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply, h, Ne.symm h]`. Consider the case `succ m ih`. Rewrite using `[pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]`.
-/
theorem pow_dualFam (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    ((Matrix.of (dualFam E) : Matrix (Fin n) (Fin n) (Module.End ℂ (Module.Dual ℂ V))) ^ m) a b φ v =
      φ (((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) b a v) := by
  induction m generalizing a b φ v with
  | zero =>
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ m ih =>
    rw [pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]

end Dual

/- English proof (translation)
Proceed by induction on `m generalizing a b with`. Consider the case `zero => simp [epow, Matrix.one_apply]`. Consider the case `succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]`.
-/
theorem epow_eq_pow {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

/- English proof (translation)
Introduce `n V _ _ E hE ev x hlow hdiag m v`. Establish `hHW : Formalism.REAL.IsHW (dualFam E) x ev` using `⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag], fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩`. Establish `h1` using `GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m`. Establish `h2` using `congrArg (fun φ : Module.Dual ℂ V => φ v) h1`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2`.

Establish `hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m = ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b`. Establish `: (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x`. Use function extensionality and compare the values at `c`. Simplify using `only [Formalism.REAL.lsh]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[GlobalTheory.Dec.gelfVal, this]`. Rewrite using `[hval, ← h2, gelA, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]`.
-/
theorem ev_gelA : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
    (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) →
    ∀ (m : ℕ) (v : V), ev (gelA E m v) =
      GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  intro n V _ _ E hE ev x hlow hdiag m v
  have hHW : Formalism.REAL.IsHW (dualFam E) x ev :=
    ⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag],
      fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩
  have h1 := GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m
  have h2 := congrArg (fun φ : Module.Dual ℂ V => φ v) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2
  have hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m =
      ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b := by
    have : (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x := by
      funext c
      simp only [Formalism.REAL.lsh]
      ring
    rw [GlobalTheory.Dec.gelfVal, this]
  rw [hval, ← h2, gelA, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]

end GlobalTheory.CompanionTheory.EvGel
