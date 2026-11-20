import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Swap

variable {F : Type*} [Field F] {n k : ℕ}

/- English proof (translation)
Take `⟨x, hx, hI, hlin⟩` from `hu`. Conclude with `⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩`.
-/
theorem comp_mem_incidence {I : Ideal (MvPolynomial (Fin n) F)} {u : Fin k × Fin n → AlgebraicClosure F}
    (hu : u ∈ incidence I k) (τ : Equiv.Perm (Fin k)) : u ∘ Prod.map τ id ∈ incidence I k := by
  obtain ⟨x, hx, hI, hlin⟩ := hu
  exact ⟨x, hx, hI, fun i => by simpa using hlin (τ i)⟩

/- English proof (translation)
Use `(hf.2 _).mp fun u hu => ?_` and prove the remaining obligations. Rewrite using `[aeval_rename]`. Conclude with `(hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)`.
-/
theorem IsChowForm.dvd_rename {I : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) : f ∣ rename (Prod.map τ id) f := by
  refine (hf.2 _).mp fun u hu => ?_
  rw [aeval_rename]
  exact (hf.2 f).mpr dvd_rfl _ (comp_mem_incidence hu τ)

/- English proof (translation)
Rewrite using `[rename_rename]`. Both sides reduce to the same expression.
-/
theorem rename_prodMap_mul (σ τ : Equiv.Perm (Fin k)) (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map (σ * τ) id) p = rename (Prod.map σ id) (rename (Prod.map τ id) p) := by
  rw [rename_rename]
  rfl

/- English proof (translation)
Establish `: Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id`. Use function extensionality and compare the values at `ij`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `rename_id_apply p`.
-/
theorem rename_prodMap_one (p : MvPolynomial (Fin k × Fin n) F) :
    rename (Prod.map ⇑(1 : Equiv.Perm (Fin k)) id) p = p := by
  have : Prod.map ⇑(1 : Equiv.Perm (Fin k)) (id : Fin n → Fin n) = id := by
    funext ij
    rfl
  rw [this]
  exact rename_id_apply p

/- English proof (translation)
Take `⟨a, ha⟩` from `hf.dvd_rename τ`. Take `⟨b, hb⟩` from `hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))`. Establish `hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f`. Rewrite using `[← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]`. Establish `hab : a * rename (Prod.map τ id) b = 1`.

Establish `h1 : f * (a * rename (Prod.map τ id) b) = f * 1`. Rewrite using `[mul_one, ← mul_assoc, ← ha]`. Use `conv_rhs => rw [← hback, hb]`. Rewrite using `[map_mul]`. Conclude with `mul_left_cancel₀ hf.1 h1`.

Take `⟨c, -, rfl⟩` from `(isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)`. Conclude with `⟨c, by rw [ha, mul_comm]⟩`.
-/
theorem IsChowForm.rename_eq_C_mul {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (τ : Equiv.Perm (Fin k)) :
    ∃ c : F, rename (Prod.map τ id) f = C c * f := by
  obtain ⟨a, ha⟩ := hf.dvd_rename τ
  obtain ⟨b, hb⟩ := hf.dvd_rename (τ⁻¹ : Equiv.Perm (Fin k))
  have hback : rename (Prod.map τ id) (rename (Prod.map ⇑(τ⁻¹ : Equiv.Perm (Fin k)) id) f) = f := by
    rw [← rename_prodMap_mul, mul_inv_cancel, rename_prodMap_one]
  have hab : a * rename (Prod.map τ id) b = 1 := by
    have h1 : f * (a * rename (Prod.map τ id) b) = f * 1 := by
      rw [mul_one, ← mul_assoc, ← ha]
      conv_rhs => rw [← hback, hb]
      rw [map_mul]
    exact mul_left_cancel₀ hf.1 h1
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (IsUnit.of_mul_eq_one _ hab)
  exact ⟨c, by rw [ha, mul_comm]⟩

/- English proof (translation)
Take `⟨c, hc⟩` from `hf.rename_eq_C_mul (Equiv.swap x y)`. Use `⟨c, ?_, hc⟩` and prove the remaining obligations. Establish `h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f`. Rewrite using `[rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]`. Rewrite `h2` using `[Equiv.swap_mul_self, rename_prodMap_one]`.

Establish `h3 : (C (c ^ 2) - 1) * f = 0`. Rewrite using `[sub_mul, ← h2, one_mul, sub_self]`. Establish `h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F)` using `(mul_eq_zero.mp h3).resolve_right hf.1`. Rewrite `h4` using `[sub_eq_zero, ← C_1]`. Conclude with `C_injective _ _ h4`.
-/
theorem IsChowForm.rename_swap {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (x y : Fin k) :
    ∃ c : F, c ^ 2 = 1 ∧ rename (Prod.map (Equiv.swap x y) id) f = C c * f := by
  obtain ⟨c, hc⟩ := hf.rename_eq_C_mul (Equiv.swap x y)
  refine ⟨c, ?_, hc⟩
  have h2 : rename (Prod.map (Equiv.swap x y * Equiv.swap x y) id) f = C (c ^ 2) * f := by
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hc, ← mul_assoc, ← C_mul, sq]
  rw [Equiv.swap_mul_self, rename_prodMap_one] at h2
  have h3 : (C (c ^ 2) - 1) * f = 0 := by
    rw [sub_mul, ← h2, one_mul, sub_self]
  have h4 : C (c ^ 2) - 1 = (0 : MvPolynomial (Fin k × Fin n) F) :=
    (mul_eq_zero.mp h3).resolve_right hf.1
  rw [sub_eq_zero, ← C_1] at h4
  exact C_injective _ _ h4

/- English proof (translation)
Introduce `F _ n k I f hf τ`. Proceed by induction on `τ using Equiv.Perm.swap_induction_on with`. Consider the case `one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩`. Consider the case `swap_mul σ x y _ ih`. Take `⟨c, hc2, hc⟩` from `ih`.

Take `⟨d, hd2, hd⟩` from `hf.rename_swap x y`. Use `⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩` and prove the remaining obligations. Rewrite using `[rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chowFormSwap : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring

end Swap

end

end GroundTheory.Heights₂.Heights
