import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
The claim follows from `hσ.2.1 _ (exp_smul_mem_UJset hX t) w`.
-/
theorem norm_orbit_apply (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (t : ℝ) (w : H) : ‖σ (NormedSpace.exp ((t : ℂ) • X)) w‖ = ‖w‖ :=
  hσ.2.1 _ (exp_smul_mem_UJset hX t) w

/- English proof (translation)
Establish `key : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) = fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (v : H))`. Use function extensionality and compare the values at `s`. Establish `hc : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X)` using `((Commute.refl X).smul_left _).smul_right _`. Establish `hsum : ((s : ℂ) • X) = (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X`. Rewrite using `[← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, Matrix.exp_add_of_commute _ _ hc, hσ.1.2 _ (exp_smul_mem_UJset hX t) _ (exp_smul_mem_UJset hX (s - t))]`. Both sides reduce to the same expression.

Rewrite using `[key]`. Establish `h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) ((actM E X v : D) : H) (t - t)`. Rewrite using `[sub_self]`. Conclude with `hD.deriv X hX v`. Establish `h1` using `HasDerivAt.comp_sub_const t t h0`.

Conclude with `((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1`.
-/
theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) ((actM E X v : D) : H)) t := by

  have key : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (v : H)) := by
    funext s
    have hc : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
      ((Commute.refl X).smul_left _).smul_right _
    have hsum : ((s : ℂ) • X) = (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X := by
      rw [← add_smul]; congr 1; push_cast; ring
    rw [hsum, Matrix.exp_add_of_commute _ _ hc,
      hσ.1.2 _ (exp_smul_mem_UJset hX t) _ (exp_smul_mem_UJset hX (s - t))]
    rfl
  rw [key]
  have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      ((actM E X v : D) : H) (t - t) := by
    rw [sub_self]; exact hD.deriv X hX v
  have h1 := HasDerivAt.comp_sub_const t t h0
  exact ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `t`.

Rewrite using `[(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]`.
-/
theorem iteratedDeriv_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]

/- English proof (translation)
Apply `contDiff_of_differentiable_iteratedDeriv` to reduce the goal to its premises. Introduce `m _`. Rewrite using `[iteratedDeriv_orbit hσ hD hX v m]`. Conclude with `fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt`.
-/
theorem contDiff_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_orbit hσ hD hX v m]
  exact fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt

end Rep

end ReciprocityTheory.ChartRestriction.DS
