import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll

open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.Col

section Kron

variable {ι : Type} [Fintype ι] [DecidableEq ι] {r : ι → ℕ}

def kron (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : Matrix (∀ τ, Fin (r τ)) (∀ τ, Fin (r τ)) ℝ :=
  Matrix.of fun I I' => ∏ τ, A τ (I τ) (I' τ)

/- English proof (translation)
Use extensionality with `I I''`. Simplify using `only [kron, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Conclude with `Finset.sum_congr rfl fun I' _ => Finset.prod_mul_distrib.symm`.
-/
theorem kron_mul (A B : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : kron A * kron B = kron fun τ => A τ * B τ := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun I' _ => Finset.prod_mul_distrib.symm

/- English proof (translation)
Use extensionality with `I I'`. Simplify using `only [kron, Matrix.of_apply]`. Distinguish the cases in `h : I = I'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.one_apply_ne h]`. Take `⟨τ, hτ⟩` from `Function.ne_iff.1 h`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ τ) (Matrix.one_apply_ne hτ)`.
-/
theorem kron_one : kron (fun τ => (1 : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)) = 1 := by
  ext I I'
  simp only [kron, Matrix.of_apply]
  by_cases h : I = I'
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (Matrix.one_apply_ne hτ)

/- English proof (translation)
Use extensionality with `I I'`. Simplify using `only [kron, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Finset.prod_mul_distrib`.
-/
theorem kron_smul (c : ι → ℝ) (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) : kron (fun τ => c τ • A τ) = (∏ τ, c τ) • kron A := by
  ext I I'
  simp only [kron, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.prod_mul_distrib

def kronDet : (∀ τ, GL (Fin (r τ)) ℝ) →* ℝ where
  toFun g := (kron fun τ => ((g τ : GL (Fin (r τ)) ℝ) : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)).det
  map_one' := by
    have : (fun τ => (((1 : ∀ τ, GL (Fin (r τ)) ℝ) τ : GL (Fin (r τ)) ℝ) : Matrix (Fin (r τ)) (Fin (r τ)) ℝ)) = fun τ => 1 := by
      funext τ; rfl
    rw [this, kron_one, Matrix.det_one]
  map_mul' g h := by
    rw [← Matrix.det_mul, kron_mul]
    rfl

/- English proof (translation)
Use `show (kron fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) : Matrix (Fin (r σ)) (Fin (r σ)) ℝ)).det = _`. Establish `h : (fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) : Matrix (Fin (r σ)) (Fin (r σ)) ℝ)) = fun σ => (if σ = τ then (t : ℝ) else 1) • (1 : Matrix (Fin (r σ)) (Fin (r σ)) ℝ)`. Use function extensionality and compare the values at `σ`. Distinguish the cases in `hσ : σ = τ`. Substitute `hσ` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same, if_pos rfl, brpSc_coe]`. Rewrite using `[Pi.mulSingle_eq_of_ne hσ, if_neg hσ, one_smul]`. Both sides reduce to the same expression. Rewrite using `[h, kron_smul, kron_one, Finset.prod_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ), Matrix.det_smul, Matrix.det_one, mul_one, zpow_natCast]`.
-/
theorem kronDet_scalar (τ : ι) (t : ℝˣ) :
    kronDet (r := r) (Pi.mulSingle τ (brpSc ℝ t)) = (t : ℝ) ^ ((Fintype.card (∀ τ, Fin (r τ)) : ℕ) : ℤ) := by
  show (kron fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) :
    Matrix (Fin (r σ)) (Fin (r σ)) ℝ)).det = _
  have h : (fun σ => (((Pi.mulSingle τ (brpSc ℝ t) : ∀ τ, GL (Fin (r τ)) ℝ) σ : GL (Fin (r σ)) ℝ) :
      Matrix (Fin (r σ)) (Fin (r σ)) ℝ)) = fun σ => (if σ = τ then (t : ℝ) else 1) • (1 : Matrix (Fin (r σ)) (Fin (r σ)) ℝ) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ
      rw [Pi.mulSingle_eq_same, if_pos rfl, brpSc_coe]
    · rw [Pi.mulSingle_eq_of_ne hσ, if_neg hσ, one_smul]; rfl
  rw [h, kron_smul, kron_one, Finset.prod_ite_eq' Finset.univ τ, if_pos (Finset.mem_univ τ), Matrix.det_smul, Matrix.det_one, mul_one,
    zpow_natCast]

/- English proof (translation)
Set `g : ∀ τ, GL (Fin (r τ)) ℝ` to `fun τ => brpGL ℝ (A τ) (isUnit_iff_ne_zero.2 (hA τ))`. Establish `h0` using `Finset.map_noncommProd Finset.univ (fun i => Pi.mulSingle i (g i)) (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j) (kronDet (r := r))`. Rewrite `h0` using `[Finset.noncommProd_mulSingle g, Finset.noncommProd_eq_prod]`. Establish `h1 : kronDet g = (kron A).det` using `rfl`. Rewrite `h0` using `[h1]`.

Establish `h2 : ∀ τ, kronDet (r` using `r) (Pi.mulSingle τ (g τ)) ^ r τ = (A τ).det ^ ((Fintype.card (∀ τ, Fin (r τ)) : ℕ) : ℤ) := fun τ => glChar_pow ℝ ((kronDet (r := r)).comp (MonoidHom.mulSingle (fun τ => GL (Fin (r τ)) ℝ) τ)) _ (kronDet_scalar τ) (g τ)`. Establish `hne : ∀ τ, kronDet (r` using `r) (Pi.mulSingle τ (g τ)) ≠ 0 := by`. Introduce `τ h`. Use `h2 τ` as an intermediate fact. Rewrite `this` using `[h, zero_pow (hr τ).ne']`.

Conclude with `(zpow_ne_zero _ (hA τ)) this.symm`. Establish `hD : (0 : ℝ) < (Fintype.card (∀ τ, Fin (r τ)) : ℝ)`. Establish `: Nonempty (∀ τ, Fin (r τ))` using `⟨fun τ => ⟨0, hr τ⟩⟩`. Conclude with `Fintype.card_pos` after adjusting the coercions. Rewrite using `[h0, Real.log_prod (fun τ _ => hne τ), Finset.sum_div]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h3` using `congrArg Real.log (h2 τ)`. Rewrite `h3` using `[Real.log_pow, Real.log_zpow]`. Establish `hrτ : (0 : ℝ) < (r τ : ℝ)` using `by exact_mod_cast hr τ`. Move the coercions through the operations in `at h3`.

Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_kron (A : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) ℝ) (hA : ∀ τ, (A τ).det ≠ 0) (hr : ∀ τ, 0 < r τ) :
    Real.log (kron A).det / (Fintype.card (∀ τ, Fin (r τ)) : ℝ) = ∑ τ, Real.log (A τ).det / (r τ : ℝ) := by
  let g : ∀ τ, GL (Fin (r τ)) ℝ := fun τ => brpGL ℝ (A τ) (isUnit_iff_ne_zero.2 (hA τ))
  have h0 := Finset.map_noncommProd Finset.univ (fun i => Pi.mulSingle i (g i))
    (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j) (kronDet (r := r))
  rw [Finset.noncommProd_mulSingle g, Finset.noncommProd_eq_prod] at h0
  have h1 : kronDet g = (kron A).det := rfl
  rw [h1] at h0
  have h2 : ∀ τ, kronDet (r := r) (Pi.mulSingle τ (g τ)) ^ r τ = (A τ).det ^ ((Fintype.card (∀ τ, Fin (r τ)) : ℕ) : ℤ) := fun τ =>
    glChar_pow ℝ ((kronDet (r := r)).comp (MonoidHom.mulSingle (fun τ => GL (Fin (r τ)) ℝ) τ)) _ (kronDet_scalar τ) (g τ)
  have hne : ∀ τ, kronDet (r := r) (Pi.mulSingle τ (g τ)) ≠ 0 := by
    intro τ h
    have := h2 τ
    rw [h, zero_pow (hr τ).ne'] at this
    exact (zpow_ne_zero _ (hA τ)) this.symm
  have hD : (0 : ℝ) < (Fintype.card (∀ τ, Fin (r τ)) : ℝ) := by
    have : Nonempty (∀ τ, Fin (r τ)) := ⟨fun τ => ⟨0, hr τ⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [h0, Real.log_prod (fun τ _ => hne τ), Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h3 := congrArg Real.log (h2 τ)
  rw [Real.log_pow, Real.log_zpow] at h3
  have hrτ : (0 : ℝ) < (r τ : ℝ) := by exact_mod_cast hr τ
  push_cast at h3
  field_simp
  linarith

end Kron

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
