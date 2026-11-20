import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace PositivityTheory.UnitaryDecomposition.X4

/- English proof (translation)
Simplify using `only [hs, trace, diag_apply, mul_apply, conjTranspose_apply]`. Rewrite using `[Finset.sum_comm]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem hs_trace {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : (hs X : ℂ) = trace (Xᴴ * X) := by
  simp only [hs, trace, diag_apply, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Rewrite using `[Jm, diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `simp only [Pi.star_apply]; split_ifs <;> simp`.
-/
theorem jm_ct {m : ℕ} (ε : Fin m → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1; funext a
  simp only [Pi.star_apply]; split_ifs <;> simp

/- English proof (translation)
Introduce `n r ε ε' ι z ⟨F, hF, FF, Fz, hz⟩`. Use `set Z : Matrix (Fin n) Unit ℂ := replicateCol Unit z with hZ`. Establish `col : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin n) ℂ), M * Z = replicateCol Unit (M *ᵥ z)` using `fun M => by`. Use extensionality with `i j`. Simplify using `[hZ, mul_apply, mulVec, dotProduct]`.

Establish `FZ : Fᴴ * Z = 0` using `by rw [col, Fz]; ext; simp`. Establish `ZF : Zᴴ * F = 0` using `by simpa using congrArg conjTranspose FZ`. Establish `ZZ : Zᴴ * Z = 1`. Use extensionality with `i j`. Establish `: ((nsq z : ℝ) : ℂ) = 1` using `by rw [hz]; simp`.

Simplify using `only [hZ, mul_apply, conjTranspose_apply, replicateCol_apply, Complex.star_def, Complex.conj_mul', Subsingleton.elim i j, one_apply_eq]`. Rewrite using `[← this, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq]`. Use `push_cast`. Both sides reduce to the same expression. Establish `S : F * Fᴴ + Z * Zᴴ = 1`.

Establish `e : Fin n ≃ Fin r ⊕ Unit` using `Fintype.equivOfCardEq (by simp [← hF.codim])`. Establish `h1 : (fromCols F Z)ᴴ * fromCols F Z = 1`. Rewrite using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, FF, FZ, ZF, ZZ, fromBlocks_one]`. Establish `h2` using `(mul_eq_one_comm_of_equiv e.symm).1 h1`. Rewrite `h2` using `[conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]`. Then use the resulting hypothesis.

Establish `FJZ : Fᴴ * Jm ε * Z = 0` using `by rw [col, hF.perp]; ext; simp`. Establish `ZJF : Zᴴ * Jm ε * F = 0`. Use `congrArg conjTranspose FJZ` as an intermediate fact. Simplify `this` using `[jm_ct, Matrix.mul_assoc]`. Establish `ZJZ : Zᴴ * Jm ε * Z = 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.mul_assoc, col, Subsingleton.elim i j, one_apply_eq, ← hF.one]`. Simplify using `[hZ, mul_apply, dotProduct]`. Establish `JZ : Jm ε * Z = Z`. Rewrite using `[← Matrix.one_mul (Jm ε * Z), ← S, Matrix.add_mul, Matrix.mul_assoc F, Matrix.mul_assoc Z, ← Matrix.mul_assoc Fᴴ, ← Matrix.mul_assoc Zᴴ, FJZ, ZJZ]`.

Simplify using the standard rewrite rules. Establish `A : ∀ h, umat (ι h) = F * umat h * Fᴴ + Z * Zᴴ` using `fun h => by`. Rewrite using `[← Matrix.mul_one (umat (ι h)), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.act, col, hF.fix]`. Establish `hsF : ∀ M : Matrix (Fin r) (Fin r) ℂ, trace ((F * M * Fᴴ)ᴴ * (F * M * Fᴴ)) = trace (Mᴴ * M)` using `fun M => by`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc Fᴴ F, FF, Matrix.one_mul, trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc, FF, Matrix.mul_one]`. Establish `cA : Continuous fun h => umat (ι h)`. Simplify using `only [A]`. Conclude with `((continuous_const.matrix_mul Formalism.MainNotions.BridgeCSchur.continuous_umat).matrix_mul continuous_const).add continuous_const`.

Use `⟨⟨?_, fun h => ?_⟩, fun h => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cA, ?_⟩)` and prove the remaining obligations. Establish `: Continuous fun h => umat (ι h⁻¹)` using `cA.comp continuous_inv`. Conclude with `this.congr fun h => by rw [map_inv]; rfl`. Establish `: umat (ι h) - 1 = F * (umat h - 1) * Fᴴ`.

Rewrite using `[A, ← S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Conclude with `(by rw [hs_trace, hs_trace, this, hsF] : (hs (umat (ι h) - 1) : ℂ) = hs (umat h - 1))` after adjusting the coercions. Establish `: (hs (umat (ι h)) : ℂ) = hs (umat h) + 1`. Rewrite using `[hs_trace, hs_trace, A, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, trace_add, hsF]`.

Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Fᴴ Z, FZ, ← Matrix.mul_assoc Zᴴ F, ZF, ← Matrix.mul_assoc Zᴴ Z, ZZ, Matrix.one_mul]`. Simplify using `[trace_mul_comm Z, ZZ]`. Conclude with `this` after adjusting the coercions. Establish `gZ : umat g * Z = Z` using `by rw [col, hg]`.

Establish `gJ : (umat g)ᴴ * Jm ε * umat g = Jm ε` using `g.2`. Establish `ZgF : Zᴴ * (umat g * F) = 0`. Establish `h1 : Zᴴ = Zᴴ * (umat g)ᴴ * Jm ε`. Rewrite using `[← conjTranspose_mul, gZ, ← jm_ct ε, ← conjTranspose_mul, JZ]`. Combine the equalities or inequalities in the displayed calculation.

Establish `gF : umat g * F = F * (Fᴴ * (umat g * F))` using `by conv_lhs => rw [← Matrix.one_mul (umat g * F), ← S, Matrix.add_mul, Matrix.mul_assoc Z, ZgF, Matrix.mul_zero, add_zero, Matrix.mul_assoc]`. Use `set h := Fᴴ * (umat g * F) with hh`. Establish `hU : inUJ ε' h` using `by show hᴴ * Jm ε' * h = Jm ε'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hF.gram]`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Fᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by rw [← gF]; simp only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [gJ, hF.gram]`. Use `⟨indefiniteUnitaryMk ε' h hU, Subtype.ext (Units.ext ?_)⟩` and prove the remaining obligations. Use `show umat _ = umat g`.

Rewrite using `[A, show umat (indefiniteUnitaryMk ε' h hU) = h from rfl, ← gF]`. Use `conv_rhs => rw [← Matrix.mul_one (umat g), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gZ]`.
-/
theorem stab : ∀ {n r : ℕ} {ε : Fin n → Bool} {ε' : Fin r → Bool} (ι : UJ ε' →* UJ ε) (z : Fin n → ℂ), IsStdStab ε ε' ι z → IsNormEmb ι ∧ (∀ h, hs (umat (ι h)) = hs (umat h) + 1) ∧ ∀ g : UJ ε, umat g *ᵥ z = z → ∃ h, ι h = g := by
  intro n r ε ε' ι z ⟨F, hF, FF, Fz, hz⟩
  set Z : Matrix (Fin n) Unit ℂ := replicateCol Unit z with hZ
  have col : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin n) ℂ), M * Z = replicateCol Unit (M *ᵥ z) := fun M => by
    ext i j; simp [hZ, mul_apply, mulVec, dotProduct]
  have FZ : Fᴴ * Z = 0 := by rw [col, Fz]; ext; simp
  have ZF : Zᴴ * F = 0 := by simpa using congrArg conjTranspose FZ
  have ZZ : Zᴴ * Z = 1 := by
    ext i j
    have : ((nsq z : ℝ) : ℂ) = 1 := by rw [hz]; simp
    simp only [hZ, mul_apply, conjTranspose_apply, replicateCol_apply, Complex.star_def, Complex.conj_mul', Subsingleton.elim i j,
      one_apply_eq]
    rw [← this, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq]; push_cast; rfl
  have S : F * Fᴴ + Z * Zᴴ = 1 := by
    have e : Fin n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [← hF.codim])
    have h1 : (fromCols F Z)ᴴ * fromCols F Z = 1 := by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, FF, FZ, ZF, ZZ, fromBlocks_one]
    have h2 := (mul_eq_one_comm_of_equiv e.symm).1 h1
    rwa [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at h2
  have FJZ : Fᴴ * Jm ε * Z = 0 := by rw [col, hF.perp]; ext; simp
  have ZJF : Zᴴ * Jm ε * F = 0 := by
    have := congrArg conjTranspose FJZ
    simpa [jm_ct, Matrix.mul_assoc] using this
  have ZJZ : Zᴴ * Jm ε * Z = 1 := by
    ext i j
    rw [Matrix.mul_assoc, col, Subsingleton.elim i j, one_apply_eq, ← hF.one]
    simp [hZ, mul_apply, dotProduct]
  have JZ : Jm ε * Z = Z := by
    rw [← Matrix.one_mul (Jm ε * Z), ← S, Matrix.add_mul, Matrix.mul_assoc F, Matrix.mul_assoc Z, ← Matrix.mul_assoc Fᴴ,
      ← Matrix.mul_assoc Zᴴ, FJZ, ZJZ]; simp
  have A : ∀ h, umat (ι h) = F * umat h * Fᴴ + Z * Zᴴ := fun h => by
    rw [← Matrix.mul_one (umat (ι h)), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF.act, col, hF.fix]
  have hsF : ∀ M : Matrix (Fin r) (Fin r) ℂ, trace ((F * M * Fᴴ)ᴴ * (F * M * Fᴴ)) = trace (Mᴴ * M) := fun M => by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Fᴴ F, FF, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, FF, Matrix.mul_one]
  have cA : Continuous fun h => umat (ι h) := by
    simp only [A]
    exact ((continuous_const.matrix_mul Formalism.MainNotions.BridgeCSchur.continuous_umat).matrix_mul continuous_const).add continuous_const
  refine ⟨⟨?_, fun h => ?_⟩, fun h => ?_, fun g hg => ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨cA, ?_⟩)
    have : Continuous fun h => umat (ι h⁻¹) := cA.comp continuous_inv
    exact this.congr fun h => by rw [map_inv]; rfl
  · have : umat (ι h) - 1 = F * (umat h - 1) * Fᴴ := by
      rw [A, ← S, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
    exact_mod_cast (by rw [hs_trace, hs_trace, this, hsF] : (hs (umat (ι h) - 1) : ℂ) = hs (umat h - 1))
  · have : (hs (umat (ι h)) : ℂ) = hs (umat h) + 1 := by
      rw [hs_trace, hs_trace, A, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
        trace_add, hsF]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᴴ Z, FZ, ← Matrix.mul_assoc Zᴴ F, ZF, ← Matrix.mul_assoc Zᴴ Z, ZZ, Matrix.one_mul]
      simp [trace_mul_comm Z, ZZ]
    exact_mod_cast this
  · have gZ : umat g * Z = Z := by rw [col, hg]
    have gJ : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
    have ZgF : Zᴴ * (umat g * F) = 0 := by
      have h1 : Zᴴ = Zᴴ * (umat g)ᴴ * Jm ε := by
        rw [← conjTranspose_mul, gZ, ← jm_ct ε, ← conjTranspose_mul, JZ]
      calc _ = Zᴴ * (umat g)ᴴ * Jm ε * (umat g * F) := by rw [← h1]
        _ = Zᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [gJ, ZJF]
    have gF : umat g * F = F * (Fᴴ * (umat g * F)) := by
      conv_lhs => rw [← Matrix.one_mul (umat g * F), ← S, Matrix.add_mul, Matrix.mul_assoc Z, ZgF, Matrix.mul_zero, add_zero,
        Matrix.mul_assoc]
    set h := Fᴴ * (umat g * F) with hh
    have hU : inUJ ε' h := by
      show hᴴ * Jm ε' * h = Jm ε'
      calc hᴴ * Jm ε' * h = (F * h)ᴴ * Jm ε * (F * h) := by
            rw [← hF.gram]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = Fᴴ * ((umat g)ᴴ * Jm ε * umat g) * F := by rw [← gF]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [gJ, hF.gram]
    refine ⟨indefiniteUnitaryMk ε' h hU, Subtype.ext (Units.ext ?_)⟩
    show umat _ = umat g
    rw [A, show umat (indefiniteUnitaryMk ε' h hU) = h from rfl, ← gF]
    conv_rhs => rw [← Matrix.mul_one (umat g), ← S, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gZ]

end PositivityTheory.UnitaryDecomposition.X4
