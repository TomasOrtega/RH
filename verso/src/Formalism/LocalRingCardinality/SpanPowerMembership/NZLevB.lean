import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial
import Lemmata.GeneralBFactRightBisForm.Imports

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility

section HW

variable (R : Type) [CommRing R] {r n : ℕ}

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det]`. Establish `hM : (rowAct R (n` using `n) h).mapMatrix (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) = (Matrix.of fun p b : Fin s => (C (h (Fin.castLE hr p) (Fin.castLE hr b)) : MvPolynomial (Fin r × Fin n) R)) * Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, …`. Use `Matrix.ext fun p q => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]`.

Simplify using `only [Matrix.of_apply]`. Use `show rowAct R h (X (Fin.castLE hr p, Fin.castLE hn q)) = _`. Rewrite using `[rowAct, aeval_X]`. Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE hr) (Fin.castLE_injective hr).injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun b _ hb => ?_) (fun _ _ => rfl)` and prove the remaining obligations.

Establish `hbs : ¬ b.val < s` using `fun hlt => hb ⟨⟨b.val, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩`. Establish `: Fin.castLE hr p < b`. Rewrite using `[Fin.lt_def, Fin.val_castLE]`. Use `p.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hl _ _ this, C_0, zero_mul]`. Rewrite using `[hM, Matrix.det_mul, Matrix.det_of_lowerTriangular, map_prod]`. Both sides reduce to the same expression. Introduce `i j hij`. Establish `hij' : i < j` using `hij`.

Rewrite using `[Matrix.of_apply, hl _ _ (by rw [Fin.lt_def]; exact hij'), C_0]`.
-/
theorem rowAct_lpMinor (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    rowAct R h (lpMinor R (n := n) s hr hn) =
      C (∏ a : Fin s, h (Fin.castLE hr a) (Fin.castLE hr a)) * lpMinor R s hr hn := by
  classical
  unfold lpMinor
  rw [AlgHom.map_det]
  have hM : (rowAct R (n := n) h).mapMatrix (Matrix.of fun p q : Fin s =>
      (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) =
      (Matrix.of fun p b : Fin s => (C (h (Fin.castLE hr p) (Fin.castLE hr b)) : MvPolynomial (Fin r × Fin n) R)) *
        Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R) := by
    refine Matrix.ext fun p q => ?_
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    show rowAct R h (X (Fin.castLE hr p, Fin.castLE hn q)) = _
    rw [rowAct, aeval_X]
    symm
    refine Finset.sum_of_injOn (Fin.castLE hr) (Fin.castLE_injective hr).injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
      (fun b _ hb => ?_) (fun _ _ => rfl)
    have hbs : ¬ b.val < s := fun hlt => hb ⟨⟨b.val, hlt⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
    have : Fin.castLE hr p < b := by
      rw [Fin.lt_def, Fin.val_castLE]
      have := p.2
      omega
    rw [hl _ _ this, C_0, zero_mul]
  rw [hM, Matrix.det_mul, Matrix.det_of_lowerTriangular, map_prod]
  · rfl
  · intro i j hij
    have hij' : i < j := hij
    rw [Matrix.of_apply, hl _ _ (by rw [Fin.lt_def]; exact hij'), C_0]

def hwScal (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) : R :=
  ∏ s : Fin n, (∏ a : Fin (s.val + 1), h (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) ^ (ν s - nuNext ν s)

/- English proof (translation)
Unfold `hw hwScal`. Rewrite using `[map_prod, smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, rowAct_lpMinor R h hl, mul_pow, map_pow]`.
-/
theorem rowAct_hw (hn : n ≤ r) (ν : Fin n → ℕ) (h : Matrix (Fin r) (Fin r) R) (hl : ∀ i j, i < j → h i j = 0) :
    rowAct R h (hw R hn ν) = hwScal R hn ν h • hw R hn ν := by
  unfold hw hwScal
  rw [map_prod, smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, rowAct_lpMinor R h hl, mul_pow, map_pow]

end HW

section ML

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {A : Type*} [CommRing A] [Algebra R A]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_right_bis_form.goal1 .. | (apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption)`.
-/
theorem prod_mem_of_span (φ : ∀ i, M i →ₗ[R] A) (S : ∀ i, Set (M i)) (T : Submodule R A)
    (h : ∀ s : ∀ i, M i, (∀ i, s i ∈ S i) → ∏ i, φ i (s i) ∈ T) (m : ∀ i, M i)
    (hm : ∀ i, m i ∈ Submodule.span R (S i)) : ∏ i, φ i (m i) ∈ T := by
  first | exact Bl.general_b_fact_right_bis_form.goal1 .. | (apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_bis_form.goal1 <;> assumption)

end ML

end Formalism.BasicNotions.Examples₂.NZ
