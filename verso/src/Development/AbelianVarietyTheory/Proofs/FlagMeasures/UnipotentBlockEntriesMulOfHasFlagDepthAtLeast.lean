import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `pos eI`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

/- English proof (translation)
Use `j.isLt` as an intermediate fact. Unfold `pos wI`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Unfold `pos esI`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

/- English proof (translation)
Establish `h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1` using `by noncomm_ring`. Establish `h2 : ((g - 1) * (x - 1)) i j = 0`. Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`.

Distinguish the cases in `hl : pos k r l < pos k r i + d`. Rewrite using `[hg i l hl, zero_mul]`. Rewrite using `[hx l j (by omega), mul_zero]`. Rewrite using `[h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hij]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN

open GlobalTheory.SnMass.VolN.LeftMul in

/- English proof (translation)
Introduce `k r g x d hg hx β hβ`. Break down `β with p | a | p | a` into its components or cases. Establish `hlt : p.1.1.val < p.1.2.val` using `p.2`. Simplify using `only [degB] at hβ`. Use `show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)`.

Rewrite using `[mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [eI] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[pos_eI, pos_eI]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [degB] at hβ`. Establish `ha` using `a.isLt`. Use `show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))`.

Use function extensionality and compare the values at `l`. Rewrite using `[Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [eI, wI] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[pos_eI, pos_wI]`. Use linear arithmetic over natural numbers and integers. Establish `hlt : p.1.1.val < p.1.2.val` using `p.2`. Establish `hb` using `p.1.2.isLt`.

Simplify using `only [degB] at hβ`. Use `show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)`. Rewrite using `[mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `only [eI, esI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pos_eI, pos_esI]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [degB] at hβ`.

Establish `ha` using `a.isLt`. Use `show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im`. Rewrite using `[mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `only [eI, esI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pos_eI, pos_esI]`. Use linear arithmetic over natural numbers and integers.
-/
theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
