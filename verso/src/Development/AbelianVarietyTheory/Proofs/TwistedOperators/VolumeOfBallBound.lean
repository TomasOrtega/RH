import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardLeOfSeparated

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.VolBallPf

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SeparatedSetCardBound.main`. Consider the case `exact _root_.GlobalTheory.SeparatedSetCardBound.main`. Consider the case `(apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)`.
-/
theorem double_count {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E) (hφ : Continuous φ) (W : Set G) (R r : ℝ)
    (hR : 0 ≤ R) (hr : 0 < r) (hW : ∀ g h, ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ 2 * r → h⁻¹ * g ∈ W) :
    μ {g | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
  first
  | exact @_root_.GlobalTheory.SeparatedSetCardBound.main
  | exact _root_.GlobalTheory.SeparatedSetCardBound.main
  | (apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SeparatedSetCardBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SeparatedSetCardBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SeparatedSetCardBound.main ..)

def toEuc {m : ℕ} (A : Mat m) : EuclideanSpace ℂ (Fin m × Fin m) := WithLp.toLp 2 fun p => A p.1 p.2

/- English proof (translation)
Simplify using `[toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]`.
-/
theorem norm_vec {m : ℕ} (A : Mat m) : ‖toEuc A‖ = hsn A := by
  simp [toEuc, hsn, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

/- English proof (translation)
Use extensionality with `p`. Simplify using `[toEuc]`.
-/
theorem toEuc_sub {m : ℕ} (A B : Mat m) : toEuc A - toEuc B = toEuc (A - B) := by
  ext p; simp [toEuc]

/- English proof (translation)
Unfold `toEuc`. Use `fun_prop`.
-/
theorem continuous_vec {m : ℕ} : Continuous (toEuc : Mat m → _) := by
  unfold toEuc
  fun_prop

/- English proof (translation)
Establish `hg : (umat g)ᴴ * Jm ε * umat g = Jm ε` using `g.2`. Establish `h1 : umat g * umat g⁻¹ = 1` using `determinant_character_mul_inv g`. Establish `h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`.

Unfold `hsn`. Rewrite using `[Finset.sum_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem hsn_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hsn (umat g⁻¹) = hsn (umat g) := by
  have hg : (umat g)ᴴ * Jm ε * umat g = Jm ε := g.2
  have h1 : umat g * umat g⁻¹ = 1 := determinant_character_mul_inv g
  have h2 : umat g⁻¹ = Jm ε * (umat g)ᴴ * Jm ε := by
    calc umat g⁻¹ = Jm ε * Jm ε * umat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
      _ = Jm ε * ((umat g)ᴴ * Jm ε * umat g) * umat g⁻¹ := by rw [hg]
      _ = Jm ε * (umat g)ᴴ * Jm ε * (umat g * umat g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [h2]
  unfold hsn
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `sqrt_frobenius_mul_le A B`.
-/
theorem hsn_mul {m : ℕ} (A B : Mat m) : hsn (A * B) ≤ hsn A * hsn B := sqrt_frobenius_mul_le A B

/- English proof (translation)
The claim follows from `sqrt_frobenius_add_le A B`.
-/
theorem hsn_add {m : ℕ} (A B : Mat m) : hsn (A + B) ≤ hsn A + hsn B := sqrt_frobenius_add_le A B

end GlobalTheory.SepReal.VolBallPf

namespace GlobalTheory.SepReal

open VolBallPf

/- English proof (translation)
Introduce `m ε δ R hδ hR`. Establish `hu : Continuous fun g : UJ ε => umat g` using `(isClosedEmbeddingMatrix m ε).1.continuous`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ}` using `isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const`. Use `lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)` and prove the remaining obligations.

Simplify `hδ` using `[norm_vec, hsn, umat]`. Establish `: ‖toEuc (umat g - 1)‖ < δ` using `hg`. Rewrite `this` using `[norm_vec]`. Conclude with `this.le`. Use `lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))` and prove the remaining obligations.

Establish `h1 : hsn (umat g - 1) ≤ δ` using `hg`. Establish `h2` using `hsn_add (umat g - 1) 1`. Rewrite `h2` using `[sub_add_cancel]`. Establish `h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m)` using `by linarith`. Conclude with `(Real.sqrt_le_iff.1 h3).2`.

Establish `key` using `double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le (by positivity) (fun g h hh hgh => by`. Rewrite `hh` using `[norm_vec]`. Rewrite `hgh` using `[toEuc_sub, norm_vec]`. Use `show hsn (umat (h⁻¹ * g) - 1) ≤ δ`. Establish `h1 : umat h⁻¹ * umat h = 1`.

Use `determinant_character_mul_inv h⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `this`. Establish `h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h)`. Rewrite using `[Matrix.mul_sub, h1]`.

Both sides reduce to the same expression. Rewrite using `[h2]`. Use `(hsn_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hsn_inv]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2`. Rewrite using `[finrank_real_of_complex, finrank_euclideanSpace]`. Simplify using `[sq]`. Establish `hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ` using `by field_simp; ring`. Simplify using `only [norm_vec, hfr, hq] at key`.

Conclude with `key`.
-/
theorem volBall : VolBall := by
  intro m ε δ R hδ hR
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix m ε).1.continuous
  refine ⟨?_, ?_, ?_⟩
  · have hU : IsOpen {g : UJ ε | ‖toEuc (umat g - 1)‖ < δ} :=
      isOpen_lt (continuous_vec.comp (hu.sub continuous_const)).norm continuous_const
    refine lt_of_lt_of_le (hU.measure_pos (muG ε) ⟨1, ?_⟩) (measure_mono fun g hg => ?_)
    · simpa [norm_vec, hsn, umat] using hδ
    · have : ‖toEuc (umat g - 1)‖ < δ := hg
      rw [norm_vec] at this
      exact this.le
  · refine lt_of_le_of_lt (measure_mono fun g hg => ?_) (ball_finite_measure_holds m ε ((δ + hsn (1 : Mat m)) ^ 2))
    have h1 : hsn (umat g - 1) ≤ δ := hg
    have h2 := hsn_add (umat g - 1) 1
    rw [sub_add_cancel] at h2
    have h3 : hsn (umat g) ≤ δ + hsn (1 : Mat m) := by linarith
    exact (Real.sqrt_le_iff.1 h3).2
  · have key := double_count (muG ε) (fun g : UJ ε => toEuc (umat g)) (continuous_vec.comp hu) (nbh ε δ) R (δ / (2 * R)) hR.le
      (by positivity) (fun g h hh hgh => by
        rw [norm_vec] at hh
        rw [toEuc_sub, norm_vec] at hgh
        show hsn (umat (h⁻¹ * g) - 1) ≤ δ
        have h1 : umat h⁻¹ * umat h = 1 := by
          have := determinant_character_mul_inv h⁻¹
          rw [inv_inv] at this
          exact this
        have h2 : umat (h⁻¹ * g) - 1 = umat h⁻¹ * (umat g - umat h) := by
          rw [Matrix.mul_sub, h1]; rfl
        rw [h2]
        refine (hsn_mul _ _).trans ?_
        rw [hsn_inv]
        calc hsn (umat h) * hsn (umat g - umat h) ≤ R * (2 * (δ / (2 * R))) :=
              mul_le_mul hh hgh (Real.sqrt_nonneg _) hR.le
          _ = δ := by field_simp)
    have hfr : Module.finrank ℝ (EuclideanSpace ℂ (Fin m × Fin m)) = 2 * m ^ 2 := by
      rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [sq]
    have hq : (R + δ / (2 * R)) / (δ / (2 * R)) = 1 + 2 * R ^ 2 / δ := by field_simp; ring
    simp only [norm_vec, hfr, hq] at key
    exact key

end GlobalTheory.SepReal

end
