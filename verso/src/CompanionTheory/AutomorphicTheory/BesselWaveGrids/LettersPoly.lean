import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

noncomputable section

namespace CompanionTheory.WaveGrid.LimSh

open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main

section letters

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Submodule.subset_span (Or.inl rfl)`.
-/
theorem one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[pow_succ, ← mul_one x]`. Conclude with `Submodule.mul_mem_mul hx one_mem_letters`.
-/
theorem letters_pow_succ (a : ℕ) : Letters k r ^ a ≤ Letters k r ^ (a + 1) := by
  intro x hx
  rw [pow_succ, ← mul_one x]
  exact Submodule.mul_mem_mul hx one_mem_letters

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `refl => exact le_rfl`. Consider the case `step _ ih => exact ih.trans (letters_pow_succ _)`.
-/
theorem letters_pow_mono {a d : ℕ} (h : a ≤ d) : Letters k r ^ a ≤ Letters k r ^ d := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (letters_pow_succ _)

/- English proof (translation)
Rewrite using `[pow_add]`. Conclude with `Submodule.mul_mem_mul hx hy`.
-/
theorem mul_mem_letters_pow {a d : ℕ} {x y : B.Mat k r → ℂ} (hx : x ∈ Letters k r ^ a) (hy : y ∈ Letters k r ^ d) :
    x * y ∈ Letters k r ^ (a + d) := by
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

/- English proof (translation)
The claim follows from `Submodule.subset_span (Or.inr ⟨Pi.single j 1, Pi.single i 1, Or.inl fun g _ => by simp⟩)`.
-/
theorem entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => g i j) ∈ Letters k r :=
  Submodule.subset_span (Or.inr ⟨Pi.single j 1, Pi.single i 1, Or.inl fun g _ => by simp⟩)

/- English proof (translation)
Use `Submodule.subset_span (Or.inr ⟨fun a => Formalism.QuantumDeterminants.Hpk k r a i, star (Formalism.QuantumDeterminants.Hpk k r j), Or.inr ?_⟩)` and prove the remaining obligations. Introduce `g hg`. Establish `hH : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1` using `(Formalism.QuantumDeterminants.hpkFacts k r).2.1`. Establish `hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r` using `hg`. Establish `hinv : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r`.

Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), hg', hH]`. Establish `e : Formalism.QuantumDeterminants.Hpk k r * (g⁻¹ * Formalism.QuantumDeterminants.Hpk k r) = gᴴ`. Rewrite using `[hinv, Matrix.mul_assoc _ (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.Hpk k r), hH, Matrix.mul_one, ← Matrix.mul_assoc, hH, Matrix.one_mul]`. Establish `e2` using `congrFun (congrFun e j) i`.

Rewrite `e2` using `[conjTranspose_apply]`. Rewrite using `[star_star]`. Conclude with `e2.symm`.
-/
theorem star_entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => star (g i j)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨fun a => Formalism.QuantumDeterminants.Hpk k r a i, star (Formalism.QuantumDeterminants.Hpk k r j), Or.inr ?_⟩)
  intro g hg
  have hH : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hinv : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), hg', hH]
  have e : Formalism.QuantumDeterminants.Hpk k r * (g⁻¹ * Formalism.QuantumDeterminants.Hpk k r) = gᴴ := by
    rw [hinv, Matrix.mul_assoc _ (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.Hpk k r), hH, Matrix.mul_one, ← Matrix.mul_assoc, hH,
      Matrix.one_mul]
  have e2 := congrFun (congrFun e j) i
  rw [conjTranspose_apply] at e2
  rw [star_star]
  exact e2.symm

/- English proof (translation)
Take `⟨q, hq, hcq⟩` from `hc`. Set `X : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → B.Mat k r → ℂ` to `Sum.elim (fun x g => g x.1 x.2) (fun x g => star (g x.1 x.2))`. Establish `hX : ∀ v, X v ∈ Letters k r`. Introduce and unpack `(x | x)`. Conclude with `entry_mem x.1 x.2`.

Conclude with `star_entry_mem x.1 x.2`. Establish `hpow : ∀ v (n : ℕ), X v ^ n ∈ Letters k r ^ n` using `fun v n => Submodule.pow_mem_pow _ (hX v) n`. Establish `hprod : ∀ (m : _ →₀ ℕ) (s : Finset _), (∏ v ∈ s, X v ^ m v) ∈ Letters k r ^ (∑ v ∈ s, m v)`. Introduce `m s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `mul_mem_letters_pow (hpow a _) ih`. Establish `e1 : c = ∑ m ∈ q.support, q.coeff m • ∏ v ∈ m.support, X v ^ m v`.

Use function extensionality and compare the values at `g`. Rewrite using `[hcq g, MvPolynomial.eval_eq, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Finset.prod_apply, smul_eq_mul]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases v with x | x <;> rfl`. Rewrite using `[e1]`. Use `Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (letters_pow_mono ?_ (hprod m m.support))` and prove the remaining obligations. Conclude with `(MvPolynomial.le_totalDegree hm).trans hq`.
-/
theorem polyDeg_mem {e : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg e c) : c ∈ Letters k r ^ e := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  let X : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
      B.Mat k r → ℂ := Sum.elim (fun x g => g x.1 x.2) (fun x g => star (g x.1 x.2))
  have hX : ∀ v, X v ∈ Letters k r := by
    rintro (x | x)
    · exact entry_mem x.1 x.2
    · exact star_entry_mem x.1 x.2
  have hpow : ∀ v (n : ℕ), X v ^ n ∈ Letters k r ^ n := fun v n => Submodule.pow_mem_pow _ (hX v) n
  have hprod : ∀ (m : _ →₀ ℕ) (s : Finset _), (∏ v ∈ s, X v ^ m v) ∈ Letters k r ^ (∑ v ∈ s, m v) := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_letters_pow (hpow a _) ih
  have e1 : c = ∑ m ∈ q.support, q.coeff m • ∏ v ∈ m.support, X v ^ m v := by
    funext g
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rcases v with x | x <;> rfl
  rw [e1]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (letters_pow_mono ?_ (hprod m m.support))
  exact (MvPolynomial.le_totalDegree hm).trans hq

end letters

end CompanionTheory.WaveGrid.LimSh
