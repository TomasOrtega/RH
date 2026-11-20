import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private noncomputable def refl {n : ℕ} (z : Fin n → ℂˣ) : Fin n → ℂˣ :=
  fun i => (Units.map (starRingEnd ℂ).toMonoidHom (z i))⁻¹

private noncomputable def star' {n : ℕ} (p : LaurentRing n) : LaurentRing n :=
  p.coeff.sum fun l c => AddMonoidAlgebra.single (-l) ((starRingEnd ℂ) c)

/- English proof (translation)
Simplify using `[refl]`.
-/
private theorem refl_val {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n) :
    ((refl z i : ℂˣ) : ℂ) = ((starRingEnd ℂ) (z i : ℂ))⁻¹ := by
  simp [refl]

/- English proof (translation)
Rewrite using `[star', map_finsuppSum, evalAt_apply, map_finsuppSum]`. Use `Finsupp.sum_congr ?_` and prove the remaining obligations. Introduce `l _`. Rewrite using `[evalAt_single, map_mul, monomialChar_apply, monomialChar_apply, map_prod]`. Use `congr 1`.

Use `Finset.prod_congr rfl ?_` and prove the remaining obligations. Introduce `i _`. Simplify using `[refl_val, Units.val_zpow_eq_zpow_val, zpow_neg, map_zpow₀, map_inv₀]`.
-/
private theorem evalAt_star' {n : ℕ} (p : LaurentRing n) (z : Fin n → ℂˣ) :
    evalAt z (star' p) = (starRingEnd ℂ) (evalAt (refl z) p) := by
  rw [star', map_finsuppSum, evalAt_apply, map_finsuppSum]
  refine Finsupp.sum_congr ?_
  intro l _
  rw [evalAt_single, map_mul, monomialChar_apply, monomialChar_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [refl_val, Units.val_zpow_eq_zpow_val, zpow_neg, map_zpow₀, map_inv₀]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem refl_comp {n : ℕ} (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    refl (z ∘ σ) = refl z ∘ σ := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[refl_val, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz i]`. Simplify using the standard rewrite rules.
-/
private theorem refl_eq {n : ℕ} (z : Fin n → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ = 1) : refl z = z := by
  funext i
  apply Units.ext
  rw [refl_val, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz i]
  simp

end UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `n p hp`. Use `⟨star' p, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Introduce `σ`. Use `eq_of_forall_evalAt fun z => ?_` and prove the remaining obligations. Rewrite using `[evalAt_permAct, evalAt_star', evalAt_star', refl_comp, ← evalAt_permAct, hp σ]`.

Rewrite using `[evalAt_star', refl_eq z hz]`.
-/
theorem UpperTheory.Gal.Gen.starEx_pf :
    UpperTheory.Gal.Gen.StarEx := by
  intro n p hp
  refine ⟨star' p, ?_, fun z hz => ?_⟩
  · intro σ
    refine eq_of_forall_evalAt fun z => ?_
    rw [evalAt_permAct, evalAt_star', evalAt_star', refl_comp, ← evalAt_permAct, hp σ]
  · rw [evalAt_star', refl_eq z hz]
