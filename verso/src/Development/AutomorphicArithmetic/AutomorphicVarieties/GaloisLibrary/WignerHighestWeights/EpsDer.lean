import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Establish `e : (Equiv.swap a b * σ).symm b = σ.symm a`. Simplify using `[Equiv.Perm.mul_def, Equiv.swap_apply_right]`. Rewrite using `[e]`. Use function extensionality and compare the values at `j`. Simplify using `only [Function.update_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.eq_symm_apply]`.

Distinguish the cases in `h1 : σ j = a`. Establish `h2 : σ j ≠ b` using `h1 ▸ hab`. Simplify using `[h1, hab]`. Distinguish the cases in `h2 : σ j = b`. Simplify using `[h1, h2, Equiv.swap_apply_right]`.

Simplify using `[h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]`.
-/
private theorem update_swap_mul_eq_update {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    Function.update (⇑(Equiv.swap a b * σ)) ((Equiv.swap a b * σ).symm b) a
      = Function.update (⇑σ) (σ.symm b) a := by
  have e : (Equiv.swap a b * σ).symm b = σ.symm a := by
    simp [Equiv.Perm.mul_def, Equiv.swap_apply_right]
  rw [e]
  funext j
  simp only [Function.update_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.eq_symm_apply]
  by_cases h1 : σ j = a
  · have h2 : σ j ≠ b := h1 ▸ hab
    simp [h1, hab]
  · by_cases h2 : σ j = b
    · simp [h1, h2, Equiv.swap_apply_right]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

/- English proof (translation)
Use `split_ifs with hab`. Substitute `hab` using the available equality. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `Function.update_eq_self (σ.symm a) (⇑σ)` as an intermediate fact. Simplify using `only [Equiv.apply_symm_apply] at this`.

Rewrite using `[this]`. Establish `key : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) = -((Equiv.Perm.sign (Equiv.mulLeft (Equiv.swap a b) σ) : ℤ) • h (Function.update (⇑(Equiv.mulLeft (Equiv.swap a b) σ)) ((Equiv.mulLeft (Equiv.swap a b) σ).symm b) a))`. Introduce `σ`. Simplify using `only [Equiv.coe_mulLeft]`. Rewrite using `[update_swap_mul_eq_update σ hab, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]`.

Simplify using the standard rewrite rules. Use `set S := ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) with hSdef`. Establish `hS : S = -S` using `by conv_lhs => rw [hSdef, Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_neg_distrib, Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b)) (fun τ => (Equiv.Perm.sign τ : ℤ) • h (Function.update (⇑τ) (τ.symm b) a))]`. Establish `h2 : (2:ℂ) • S = 0`. Rewrite using `[two_smul]`.

Use `nth_rewrite 2 [hS]`. Conclude with `add_neg_cancel S`. Conclude with `(smul_eq_zero.mp h2).resolve_left two_ne_zero`.
-/
private theorem sum_sign_smul_update_eq_ite {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (h : (Fin n → Fin n) → M) (a b : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
      = if a = b then ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ else 0 := by
  split_ifs with hab
  · subst hab
    refine Finset.sum_congr rfl fun σ _ => ?_
    have := Function.update_eq_self (σ.symm a) (⇑σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
  · have key : ∀ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a)
          = -((Equiv.Perm.sign (Equiv.mulLeft (Equiv.swap a b) σ) : ℤ) •
              h (Function.update (⇑(Equiv.mulLeft (Equiv.swap a b) σ))
                ((Equiv.mulLeft (Equiv.swap a b) σ).symm b) a)) := by
      intro σ
      simp only [Equiv.coe_mulLeft]
      rw [update_swap_mul_eq_update σ hab, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
      simp
    set S := ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_neg_distrib,
        Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
          (fun τ => (Equiv.Perm.sign τ : ℤ) • h (Function.update (⇑τ) (τ.symm b) a))]
    have h2 : (2:ℂ) • S = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hS]
      exact add_neg_cancel S
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.
-/
private theorem update_single_first_index_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single a (c k) 1)
      = fun j => Matrix.single (Function.update r k a j) (c j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`.
-/
private theorem update_single_col_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1:ℂ)) k (Matrix.single (r k) a 1)
      = fun j => Matrix.single (r j) (Function.update c k a j) (1:ℂ) := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]`.
-/
private theorem mul_single_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    y * Matrix.single p q (1:ℂ) = ∑ a, y a p • Matrix.single a q (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]`.
-/
private theorem single_mul_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    Matrix.single p q (1:ℂ) * y = ∑ c, y q c • Matrix.single p c (1:ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

/- English proof (translation)
Use `set h : (Fin n → Fin n) → M := fun r => μ (fun j => Matrix.single (r j) (τ j) (1:ℂ)) with hh`. Establish `inner : ∀ σ : Equiv.Perm (Fin n), ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k)) = ∑ b, ∑ a, y a b • h (Function.update (⇑σ) (σ.symm b) a)`. Introduce `σ`. Establish `hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ)` using `rfl`. Rewrite using `[hu]`.

Repeatedly rewrite using `[mul_single_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul, update_single_first_index_eq]`. Rewrite using `[← Equiv.sum_comp σ.symm]`. Simplify using `[hh]`. Repeatedly rewrite using `[inner, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `step : ∀ b : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ a, (Equiv.Perm.sign σ : ℤ) • y a b • h (Function.update (⇑σ) (σ.symm b) a) = y b b • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ`. Introduce `b`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[smul_comm ((Equiv.Perm.sign _ : ℤ)) (y _ b), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]`. Both sides reduce to the same expression.
-/
private theorem sum_sign_left_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M)
    (y : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = Matrix.trace y • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun r => μ (fun j => Matrix.single (r j) (τ j) (1:ℂ)) with hh
  have inner : ∀ σ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
        = ∑ b, ∑ a, y a b • h (Function.update (⇑σ) (σ.symm b) a) := by
    intro σ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [mul_single_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_first_index_eq]
    rw [← Equiv.sum_comp σ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ a, (Equiv.Perm.sign σ : ℤ) •
      y a b • h (Function.update (⇑σ) (σ.symm b) a)
        = y b b • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y _ b), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

/- English proof (translation)
Use `set h : (Fin n → Fin n) → M := fun c => μ (fun j => Matrix.single (σ j) (c j) (1:ℂ)) with hh`. Establish `inner : ∀ τ : Equiv.Perm (Fin n), ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y)) = ∑ b, ∑ c, y b c • h (Function.update (⇑τ) (τ.symm b) c)`. Introduce `τ`. Establish `hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ)` using `rfl`. Rewrite using `[hu]`.

Repeatedly rewrite using `[single_mul_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul, update_single_col_eq]`. Rewrite using `[← Equiv.sum_comp τ.symm]`. Simplify using `[hh]`. Repeatedly rewrite using `[inner, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.

Establish `step : ∀ b : Fin n, ∑ τ : Equiv.Perm (Fin n), ∑ c, (Equiv.Perm.sign τ : ℤ) • y b c • h (Function.update (⇑τ) (τ.symm b) c) = y b b • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • h ⇑τ`. Introduce `b`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[smul_comm ((Equiv.Perm.sign _ : ℤ)) (y b _), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]`. Both sides reduce to the same expression.
-/
private theorem sum_sign_right_mul_update_eq_trace_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M)
    (y : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = Matrix.trace y • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun c => μ (fun j => Matrix.single (σ j) (c j) (1:ℂ)) with hh
  have inner : ∀ τ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
        = ∑ b, ∑ c, y b c • h (Function.update (⇑τ) (τ.symm b) c) := by
    intro τ
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1:ℂ) := rfl
    rw [hu]
    simp_rw [single_mul_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_col_eq]
    rw [← Equiv.sum_comp τ.symm]
    simp [hh]
  simp_rw [inner, Finset.smul_sum]
  rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ τ : Equiv.Perm (Fin n), ∑ c, (Equiv.Perm.sign τ : ℤ) •
      y b c • h (Function.update (⇑τ) (τ.symm b) c)
        = y b b • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • h ⇑τ := by
    intro b
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y b _), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]
    simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]
  rfl

/- English proof (translation)
Introduce `M _ _ n μ y`. Use `show ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k - units σ τ k * y)) = 0`. Repeatedly rewrite using `[MultilinearMap.map_update_sub, Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`. Establish `L : ∀ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k)) = (Equiv.Perm.sign τ : ℤ) • (Matrix.trace y • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ))`.

Introduce `τ`. Rewrite using `[← sum_sign_left_mul_update_eq_trace_smul, Finset.smul_sum]`. Repeatedly rewrite using `[mul_smul]`. Establish `R : ∀ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y)) = (Equiv.Perm.sign σ : ℤ) • (Matrix.trace y • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ))`. Introduce `σ`.

Rewrite using `[← sum_sign_right_mul_update_eq_trace_smul, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Rewrite using `[Finset.sum_congr rfl fun τ _ => L τ, Finset.sum_comm, Finset.sum_congr rfl fun σ _ => R σ]`. Repeatedly rewrite using `[smul_comm _ (Matrix.trace y), ← Finset.smul_sum]`.

Use `congr 1`. Repeatedly rewrite using `[Finset.smul_sum, ← mul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.epsDer :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M) (y : Matrix (Fin n) (Fin n) ℂ),
      eps (fun x => ∑ k, μ (Function.update x k (y * x k - x k * y))) = 0 := by
  intro M _ _ n μ y
  show ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k - units σ τ k * y)) = 0
  simp_rw [MultilinearMap.map_update_sub, Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have L : ∀ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k))
      = (Equiv.Perm.sign τ : ℤ) • (Matrix.trace y •
          ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ)) := by
    intro τ
    rw [← sum_sign_left_mul_update_eq_trace_smul, Finset.smul_sum]
    simp_rw [mul_smul]
  have R : ∀ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y))
      = (Equiv.Perm.sign σ : ℤ) • (Matrix.trace y •
          ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ)) := by
    intro σ
    rw [← sum_sign_right_mul_update_eq_trace_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_smul]
  rw [Finset.sum_congr rfl fun τ _ => L τ, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => R σ]
  simp_rw [smul_comm _ (Matrix.trace y), ← Finset.smul_sum]
  congr 1
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_comm]
