import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory

/- English proof (translation)
Introduce `q σ g i i' hq h`. Establish `hq1 : (1 : ℤ) < q` using `by exact_mod_cast hq.one_lt`. Establish `hdet : (mat g).det = 1` using `g.2`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Establish `e00` using `congrArg (· 0 0) h`.

Establish `e01` using `congrArg (· 0 1) h`. Establish `e10` using `congrArg (· 1 0) h`. Establish `e11` using `congrArg (· 1 1) h`. Simplify using `only [tqFam] at e00 e01 e10 e11`. Establish `hi` using `i.isLt`.

Establish `hi'` using `i'.isLt`. Apply the tactic sequence `by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>`. Simplify using `only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11`. Apply `Fin.ext` to reduce the goal to its premises. Establish `hg00 : (mat g) 0 0 = 1` using `by linarith`.

Rewrite `e01` using `[hg00]`. Establish `hii : (0:ℤ) ≤ (i : ℕ)` using `by positivity`. Establish `hii' : (0:ℤ) ≤ (i' : ℕ)` using `by positivity`. Establish `hlt : ((i : ℕ) : ℤ) < q` using `by exact_mod_cast h1`. Establish `hlt' : ((i' : ℕ) : ℤ) < q` using `by exact_mod_cast h2`.

Break down `lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp` into its components or cases. It suffices to derive a contradiction. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))`. It suffices to derive a contradiction.

Use the polynomial consequences of the given equalities and inequalities. It suffices to derive a contradiction. Establish `hd : (q : ℤ) ∣ 1` using `⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩`. Use `Int.eq_one_of_dvd_one (by positivity) hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Establish `hd : (q : ℤ) ∣ 1`. Rewrite using `[← hdet]`. Conclude with `Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _) (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)`. Use `Int.eq_one_of_dvd_one (by positivity) hd` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem tqFam_cosets_distinct : ∀ (q : ℕ) (σ g : SL(2, ℤ)) (i i' : Fin (q + 1)), q.Prime →
    tqFam q σ i = mat g * tqFam q σ i' → i = i' := by
  intro q σ g i i' hq h
  have hq1 : (1 : ℤ) < q := by exact_mod_cast hq.one_lt
  have hdet : (mat g).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrArg (· 0 0) h
  have e01 := congrArg (· 0 1) h
  have e10 := congrArg (· 1 0) h
  have e11 := congrArg (· 1 1) h
  simp only [tqFam] at e00 e01 e10 e11
  have hi := i.isLt
  have hi' := i'.isLt
  by_cases h1 : (i : ℕ) < q <;> by_cases h2 : (i' : ℕ) < q <;>
    simp only [h1, h2, if_true, if_false, dg, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const] at e00 e01 e10 e11
  ·
    apply Fin.ext
    have hg00 : (mat g) 0 0 = 1 := by linarith
    rw [hg00] at e01
    have hii : (0:ℤ) ≤ (i : ℕ) := by positivity
    have hii' : (0:ℤ) ≤ (i' : ℕ) := by positivity
    have hlt : ((i : ℕ) : ℤ) < q := by exact_mod_cast h1
    have hlt' : ((i' : ℕ) : ℤ) < q := by exact_mod_cast h2
    rcases lt_trichotomy ((mat g) 0 1) 0 with hn | hz | hp
    · exfalso; nlinarith
    · rw [hz] at e01; exact_mod_cast (by linarith : ((i : ℕ) : ℤ) = (i' : ℕ))
    · exfalso; nlinarith
  · exfalso
    have hd : (q : ℤ) ∣ 1 := ⟨mat g 0 0 * mat σ 0 0 + mat g 0 1 * mat σ 1 0, by linear_combination e00⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · exfalso
    have hd : (q : ℤ) ∣ 1 := by
      rw [← hdet]
      exact Dvd.dvd.sub (Dvd.dvd.mul_right ⟨mat σ 0 0, by linear_combination -e00⟩ _)
        (Dvd.dvd.mul_left ⟨mat σ 1 0, by linear_combination -e10⟩ _)
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  · apply Fin.ext; omega

end GlobalTheory
