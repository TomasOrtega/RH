import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Mathlib.GroupTheory.Perm.Fin

/- English proof (translation)
Simplify using `[Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_succAbove, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]`.
-/
private theorem cycle_range_conjugate_succAbove {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      (j.succAbove k) = i.succAbove (τ k) := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_succAbove,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

/- English proof (translation)
Simplify using `[Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_self, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]`.
-/
private theorem cycle_range_conjugate_pivot {n : ℕ} (i j : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    ((Fin.cycleRange i)⁻¹ * Equiv.Perm.decomposeFin.symm (0, τ) * Fin.cycleRange j : Equiv.Perm (Fin (n + 1)))
      j = i := by
  simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_self,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

/- English proof (translation)
Introduce `n j`. Set `F : Fin (n + 1) × Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1))` to `fun p => (Fin.cycleRange p.1)⁻¹ * Equiv.Perm.decomposeFin.symm (0, p.2) * Fin.cycleRange j`. Establish `hinj : Function.Injective F`. Introduce and unpack `⟨i, τ⟩ ⟨i', τ'⟩ h`. Establish `hi : i = i'`.

Establish `h1` using `congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j) h`. Simplify using `only [F] at h1`. Rewrite `h1` using `[cycle_range_conjugate_pivot, cycle_range_conjugate_pivot]`. Conclude with `h1`. Substitute `hi` using the available equality.

Simplify using `only [F] at h`. Establish `h2` using `Equiv.injective _ (mul_left_cancel (mul_right_cancel h))`. Rewrite `h2` using `[Prod.mk.injEq]`. Rewrite using `[h2.2]`. Establish `hsurj : Function.Surjective F`.

Introduce `σ`. Establish `hρ : (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹) 0 = 0`. Simplify using `[Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_zero, Fin.cycleRange_self]`. Take `⟨⟨p, τ⟩, hp⟩` from `Equiv.Perm.decomposeFin.symm.surjective (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹)`. Establish `hp0 : p = 0`.

Establish `h0` using `congrArg (fun s : Equiv.Perm (Fin (n + 1)) => s 0) hp`. Simplify using `only [Equiv.Perm.decomposeFin_symm_apply_zero] at h0`. Rewrite using `[h0, hρ]`. Substitute `hp0` using the available equality. Use `⟨(σ j, τ), ?_⟩` and prove the remaining obligations.

Simplify using `only [F]`. Rewrite using `[hp]`. Use `group`. Use `⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩` and prove the remaining obligations. Introduce `i τ`.

Use `⟨?_, fun k => cycle_range_conjugate_succAbove i j τ k⟩` and prove the remaining obligations. Use `show ((Equiv.Perm.sign (F (i, τ)) : ℤ) : _) = _`. Simplify using `only [F, map_mul, map_inv, Fin.sign_cycleRange, Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, inv_pow, Int.units_inv_eq_self]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.perm_split_fin_succ :
    UpperTheory.V.Af.BA.PermSplit := by
  intro n j
  classical
  let F : Fin (n + 1) × Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) := fun p =>
    (Fin.cycleRange p.1)⁻¹ * Equiv.Perm.decomposeFin.symm (0, p.2) * Fin.cycleRange j
  have hinj : Function.Injective F := by
    rintro ⟨i, τ⟩ ⟨i', τ'⟩ h
    have hi : i = i' := by
      have h1 := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j) h
      simp only [F] at h1
      rw [cycle_range_conjugate_pivot, cycle_range_conjugate_pivot] at h1
      exact h1
    subst hi
    simp only [F] at h
    have h2 := Equiv.injective _ (mul_left_cancel (mul_right_cancel h))
    rw [Prod.mk.injEq] at h2
    rw [h2.2]
  have hsurj : Function.Surjective F := by
    intro σ
    have hρ : (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹) 0 = 0 := by
      simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_zero, Fin.cycleRange_self]
    obtain ⟨⟨p, τ⟩, hp⟩ := Equiv.Perm.decomposeFin.symm.surjective
      (Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹)
    have hp0 : p = 0 := by
      have h0 := congrArg (fun s : Equiv.Perm (Fin (n + 1)) => s 0) hp
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at h0
      rw [h0, hρ]
    subst hp0
    refine ⟨(σ j, τ), ?_⟩
    simp only [F]
    rw [hp]
    group
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_⟩
  intro i τ
  refine ⟨?_, fun k => cycle_range_conjugate_succAbove i j τ k⟩
  show ((Equiv.Perm.sign (F (i, τ)) : ℤ) : _) = _
  simp only [F, map_mul, map_inv, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign, if_pos rfl, one_mul, inv_pow, Int.units_inv_eq_self]
  push_cast
  ring
