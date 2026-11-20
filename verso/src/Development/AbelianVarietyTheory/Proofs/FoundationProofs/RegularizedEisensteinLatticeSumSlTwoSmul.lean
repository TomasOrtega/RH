import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

def rowZ (γ : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1)
  invFun x := (x.1 * γ 1 1 - x.2 * γ 1 0, -(x.1 * γ 0 1) + x.2 * γ 0 0)
  left_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h
  right_inv x := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    ext
    · simp only; linear_combination x.1 * h
    · simp only; linear_combination x.2 * h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowZ_apply (γ : SL(2, ℤ)) (x : ℤ × ℤ) :
    rowZ γ x = (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) := rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rowZ_add_smul (γ : SL(2, ℤ)) (x v : ℤ × ℤ) (r : ℤ) :
    rowZ γ (x + r • v) = rowZ γ x + r • rowZ γ v := by
  simp only [rowZ_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.mk_add_mk, Prod.smul_mk]
  ext <;> simp only <;> ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem dif_comp_rowZ (L : ℕ) (γ : SL(2, ℤ)) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => F (rowZ γ y)) = fun x => dif L (rowZ γ v) F (rowZ γ x) := by
  funext x
  simp only [dif, rowZ_add_smul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dif_const_mul (L : ℕ) (v : ℤ × ℤ) (c : ℂ) (F : ℤ × ℤ → ℂ) :
    dif L v (fun y => c * F y) = fun x => c * dif L v F x := by
  funext x
  simp only [dif, ← Finset.mul_sum]
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Clear the denominators using the available nonvanishing facts. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion repeatedly using the stated equalities. Establish an intermediate fact. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem lat_smul (j L : ℕ) (v : ℤ × ℤ) (Φ Φ' : ℤ × ℤ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ)
    (hΦ : ∀ x : ℤ × ℤ, Φ' (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x) :
    lat j 0 L v Φ (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ j *
      lat j 0 L (v.1 * γ 0 0 + v.2 * γ 1 0, v.1 * γ 0 1 + v.2 * γ 1 1) Φ' τ := by
  set D : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hD
  have hD0 : D ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [UpperHalfPlane.denom, hD] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [hD]
  set H : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hH
  have hG : (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) =
      fun y => D ^ j * H (rowZ γ y) := by
    funext y
    simp only [hH, trm, rowZ_apply, hcoe, mul_zero, neg_mul, Real.rpow_zero, Complex.ofReal_one, mul_one]
    have : (y.1 : ℂ) * ((((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / D) + y.2 =
        ((((y.1 * γ 0 0 + y.2 * γ 1 0 : ℤ)) : ℂ) * τ + ((y.1 * γ 0 1 + y.2 * γ 1 1 : ℤ) : ℂ)) / D := by
      field_simp
      push_cast
      ring
    rw [this, div_pow, inv_div]
    ring_nf
  have hdd : ∀ x, dif L v (dif L v fun y => trm j 0 ((y.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + y.2)) x =
      D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) (rowZ γ x) := by
    intro x
    rw [hG, dif_const_mul, dif_const_mul]
    simp only
    rw [dif_comp_rowZ]
    rw [show (fun x => dif L (rowZ γ v) H (rowZ γ x)) = fun x => (dif L (rowZ γ v) H) (rowZ γ x) from rfl,
      dif_comp_rowZ]
  unfold lat
  simp_rw [hdd]
  have hΦ' : ∀ x, Φ x = Φ' (rowZ γ x) := fun x => (hΦ x).symm
  simp_rw [hΦ']
  rw [Equiv.tsum_eq (rowZ γ) (fun z => Φ' z * (D ^ j * dif L (rowZ γ v) (dif L (rowZ γ v) H) z)),
    ← tsum_mul_left]
  congr 1
  funext x
  rw [hH]
  simp only [rowZ_apply]
  ring

end GlobalTheory.EisM
