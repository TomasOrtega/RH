import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped ComplexConjugate

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Submodule.subset_span (Or.inl rfl)`.
-/
theorem one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)

/- English proof (translation)
Rewrite using `[pow_succ]`. Simplify using `using Submodule.mul_mem_mul h one_mem_letters`.
-/
theorem letters_pow_succ {d : ℕ} {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) : q ∈ Letters k r ^ (d + 1) := by
  rw [pow_succ]
  simpa using Submodule.mul_mem_mul h one_mem_letters

/- English proof (translation)
Proceed by induction on `hde with`. Consider the case `refl => exact h`. Consider the case `step _ ih => exact letters_pow_succ ih`.
-/
theorem letters_pow_mono {d e : ℕ} (hde : d ≤ e) {q : B.Mat k r → ℂ} (h : q ∈ Letters k r ^ d) :
    q ∈ Letters k r ^ e := by
  induction hde with
  | refl => exact h
  | step _ ih => exact letters_pow_succ ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Submodule.mem_one]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']`. Conclude with `Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem prod_mem_pow {ι : Type} (s : Finset ι) (q : ι → B.Mat k r → ℂ) (h : ∀ i ∈ s, q i ∈ Letters k r) :
    ∏ i ∈ s, q i ∈ Letters k r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.mem_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Submodule.mul_mem_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `e : (fun g => (Z g).det) = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ i, fun g => Z g (σ i) i`. Use function extensionality and compare the values at `g`. Simplify using `[Matrix.det_apply', Finset.prod_apply]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Simplify using `using prod_mem_pow Finset.univ (fun i g => Z g (σ i) i) fun i _ => h _ _`.
-/
theorem det_mem_pow {m : ℕ} (Z : B.Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ a b, (fun g => Z g a b) ∈ Letters k r) : (fun g => (Z g).det) ∈ Letters k r ^ m := by
  have e : (fun g => (Z g).det) =
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ i, fun g => Z g (σ i) i := by
    funext g
    simp [Matrix.det_apply', Finset.prod_apply]
  rw [e]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
  simpa using prod_mem_pow Finset.univ (fun i g => Z g (σ i) i) fun i _ => h _ _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp`.
-/
theorem hpk_herm : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/- English proof (translation)
Use `Submodule.subset_span (Or.inr ⟨x, Formalism.QuantumDeterminants.Hpk k r *ᵥ y, Or.inl fun g _ => ?_⟩)` and prove the remaining obligations. Simplify using `only [Formalism.QuantumDeterminants.herm]`. Rewrite using `[Matrix.star_mulVec, hpk_herm, Matrix.dotProduct_mulVec]`.
-/
theorem herm_letter (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨x, Formalism.QuantumDeterminants.Hpk k r *ᵥ y, Or.inl fun g _ => ?_⟩)
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, hpk_herm, Matrix.dotProduct_mulVec]

/- English proof (translation)
Use `Submodule.subset_span (Or.inr ⟨y, Formalism.QuantumDeterminants.Hpk k r *ᵥ x, Or.inr fun g hg => ?_⟩)` and prove the remaining obligations. Establish `hu` using `(PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1`. Establish `hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r` using `hg`. Establish `e : gᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * g⁻¹` using `by conv_rhs => rw [← hg']`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]`.

Simplify using `only [Formalism.QuantumDeterminants.herm]`. Rewrite using `[← Matrix.star_dotProduct_star, star_star, Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_mul, hpk_herm, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]`.
-/
theorem herm_conj_letter (x y : Fin (2 * r + k + 1) → ℂ) :
    (fun g : B.Mat k r => star (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ x) y)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨y, Formalism.QuantumDeterminants.Hpk k r *ᵥ x, Or.inr fun g hg => ?_⟩)
  have hu := (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg).1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * g⁻¹ := by
    conv_rhs => rw [← hg']
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.mul_one]
  simp only [Formalism.QuantumDeterminants.herm]
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.star_mulVec, Matrix.conjTranspose_mul, hpk_herm, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

/- English proof (translation)
Establish `hl : (l : ℕ) ≤ r + 1` using `Nat.le_of_lt_succ l.isLt`. Establish `h1 : (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) ∈ Letters k r ^ (r + 1)` using `letters_pow_mono hl (det_mem_pow _ fun a b => herm_letter _ _)`. Establish `h2 : (fun g : B.Mat k r => conj (Formalism.QuantumDeterminants.Dmin k r z z' g l)) ∈ Letters k r ^ (r + 1)`. Use `det_mem_pow (k := k) (r := r) (fun g => ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl))ᴴ) fun a b => herm_conj_letter _ _` as an intermediate fact. Simplify using `only [Matrix.det_conjTranspose] at this`.

Conclude with `letters_pow_mono hl this`. Use `Submodule.mul_mem_mul h1 h2` as an intermediate fact. Rewrite `this` using `[← pow_add, show r + 1 + (r + 1) = 2 * r + 2 by ring]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Simplify using `[Complex.mul_conj]`.
-/
theorem dmin_mem (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    (fun g : B.Mat k r => ((Complex.normSq (Formalism.QuantumDeterminants.Dmin k r z z' g l) : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
  have hl : (l : ℕ) ≤ r + 1 := Nat.le_of_lt_succ l.isLt
  have h1 : (fun g : B.Mat k r => Formalism.QuantumDeterminants.Dmin k r z z' g l) ∈ Letters k r ^ (r + 1) :=
    letters_pow_mono hl (det_mem_pow _ fun a b => herm_letter _ _)
  have h2 : (fun g : B.Mat k r => conj (Formalism.QuantumDeterminants.Dmin k r z z' g l)) ∈ Letters k r ^ (r + 1) := by
    have := det_mem_pow (k := k) (r := r) (fun g => ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix
      (Fin.castLE hl) (Fin.castLE hl))ᴴ) fun a b => herm_conj_letter _ _
    simp only [Matrix.det_conjTranspose] at this
    exact letters_pow_mono hl this
  have := Submodule.mul_mem_mul h1 h2
  rw [← pow_add, show r + 1 + (r + 1) = 2 * r + 2 by ring] at this
  convert this using 1
  funext g
  simp [Complex.mul_conj]

/- English proof (translation)
Introduce `k r z z' p`. Establish `h : (fun g : B.Mat k r => ((Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2)`. Use `Submodule.sub_mem _ (dmin_mem z z' (Fin.last (r + 1))) (Submodule.smul_mem _ ((Formalism.QuantumDeterminants.Tz k r z * Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) (dmin_mem z z' ⟨r, by omega⟩))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Simplify using `[Formalism.QuantumDeterminants.Gf]`. Rewrite using `[pow_mul]`. Use `Submodule.pow_mem_pow _ h p using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.
-/
theorem generating_function_polynomial : GfPoly := by
  intro k r z z' p
  have h : (fun g : B.Mat k r => ((Formalism.QuantumDeterminants.Gf k r z z' g : ℝ) : ℂ)) ∈ Letters k r ^ (2 * r + 2) := by
    have := Submodule.sub_mem _ (dmin_mem z z' (Fin.last (r + 1)))
      (Submodule.smul_mem _ ((Formalism.QuantumDeterminants.Tz k r z * Formalism.QuantumDeterminants.Tz k r z' : ℝ) : ℂ) (dmin_mem z z' ⟨r, by omega⟩))
    convert this using 1
    funext g
    simp [Formalism.QuantumDeterminants.Gf]
  rw [pow_mul]
  convert Submodule.pow_mem_pow _ h p using 1
  funext g
  simp

end CompanionTheory.LimBd.Main
