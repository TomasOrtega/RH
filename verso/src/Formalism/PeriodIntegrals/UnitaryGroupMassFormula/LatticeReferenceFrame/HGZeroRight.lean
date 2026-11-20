import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WBasis

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WB

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := rfl

/- English proof (translation)
Simplify using `only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  simp only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hG_def, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hG_smul_left (c : I.E) (x y : Fin I.n → I.E) : hG I (c • x) y = star c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[hG_def]`.
-/
theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by simp [hG_def]

/- English proof (translation)
Simplify using `only [hG_def, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hG_sub_right (x y z : Fin I.n → I.E) : hG I x (y - z) = hG I x y - hG I x z := by
  simp only [hG_def, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hG_zero_right]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hG_add_right, ih]`.
-/
theorem hG_sum_right {ι : Type*} (s : Finset ι) (x : Fin I.n → I.E) (y : ι → Fin I.n → I.E) :
    hG I x (∑ t ∈ s, y t) = ∑ t ∈ s, hG I x (y t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hG_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hG_add_right, ih]

/- English proof (translation)
Establish `h` using `congrFun (congrFun I.J_herm i) j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h`. Conclude with `h`.
-/
theorem J_entry (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h := congrFun (congrFun I.J_herm i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
  exact h

/- English proof (translation)
Simplify using `only [hG_def, star_sum, star_mul', star_star]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[J_entry]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [J_entry]
  ring

variable {I}

/- English proof (translation)
Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)`. Use `⟨s, hs, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_cancel₀ (by exact_mod_cast hs0)]`.

Simplify using the standard rewrite rules.
-/
theorem inv_mem_Ap {p s : ℕ} (hp : p.Prime) (hs : Nat.Coprime s p) : ((s : I.E))⁻¹ ∈ Ap I p := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs)
  refine ⟨s, hs, 1, ?_⟩
  rw [mul_inv_cancel₀ (by exact_mod_cast hs0)]
  simp

end PI.ScRefExists.WB
