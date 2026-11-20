import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Use `show ∏ i, (((w (Fin.revPerm i)) ^ (-l (Fin.rev i)) : ℂˣ) : ℂ) = (starRingEnd ℂ) (∏ i, ((w i ^ l i : ℂˣ) : ℂ))`. Rewrite using `[map_prod, ← Equiv.prod_comp Fin.revPerm (fun k => (starRingEnd ℂ) ((w k ^ l k : ℂˣ) : ℂ))]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]`. Rewrite using `[← Complex.inv_eq_conj (hw _), zpow_neg, inv_zpow]`.
-/
private theorem mono_term {n : ℕ} (l : Fin n → ℤ) (w : Fin n → ℂˣ) (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    monomialChar (fun i => -l (Fin.rev i)) (w ∘ Fin.revPerm) =
      (starRingEnd ℂ) (monomialChar l w) := by
  show ∏ i, (((w (Fin.revPerm i)) ^ (-l (Fin.rev i)) : ℂˣ) : ℂ) =
    (starRingEnd ℂ) (∏ i, ((w i ^ l i : ℂˣ) : ℂ))
  rw [map_prod, ← Equiv.prod_comp Fin.revPerm (fun k => (starRingEnd ℂ) ((w k ^ l k : ℂˣ) : ℂ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  rw [← Complex.inv_eq_conj (hw _), zpow_neg, inv_zpow]

/- English proof (translation)
Rewrite using `[map_prod]`. Use `Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Conclude with `Fin.rev_lt_rev.mpr hp`.

Introduce `p hp`. Simplify using `only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Conclude with `Fin.rev_lt_rev.mpr hp`. Introduce `p _`. Simplify using the standard rewrite rules.

Introduce `p _`. Simplify using the standard rewrite rules. Introduce `p hp`. Simplify using `only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Establish `hne : Fin.rev p.2 ≠ Fin.rev p.1` using `fun h => (ne_of_lt hp) (Fin.rev_injective h).symm`.

Establish `hab : (w (Fin.rev p.2) : ℂ) ≠ (w (Fin.rev p.1) : ℂ)` using `fun h => hne (hinj (Units.val_injective h))`. Establish `ha : (w (Fin.rev p.2) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `hb : (w (Fin.rev p.1) : ℂ) ≠ 0` using `Units.ne_zero _`. Simplify using `only [map_div₀, map_sub, map_mul, Complex.conj_ofReal]`. Rewrite using `[← Complex.inv_eq_conj (hw _), ← Complex.inv_eq_conj (hw _)]`.

Generalize the expression as in `(w (Fin.rev p.2) : ℂ) = a at *`. Generalize the expression as in `(w (Fin.rev p.1) : ℂ) = b at *`. Establish `h1 : b - a ≠ 0` using `sub_ne_zero.mpr (Ne.symm hab)`. Establish `h2 : a⁻¹ - b⁻¹ ≠ 0`. Rewrite using `[inv_sub_inv ha hb]`.

Conclude with `div_ne_zero h1 (mul_ne_zero ha hb)`. Rewrite using `[div_eq_div_iff h1 h2]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem pair_term {n : ℕ} (t : ℝ) (w : Fin n → ℂˣ) (hinj : Function.Injective w)
    (hw : ∀ i, ‖(w i : ℂ)‖ = 1) :
    ∏ p ∈ prs n, ((w (Fin.rev p.1) : ℂ) - (t : ℂ) * (w (Fin.rev p.2) : ℂ)) /
        ((w (Fin.rev p.1) : ℂ) - (w (Fin.rev p.2) : ℂ)) =
      (starRingEnd ℂ) (∏ p ∈ prs n, ((w p.1 : ℂ) - (t : ℂ) * (w p.2 : ℂ)) /
        ((w p.1 : ℂ) - (w p.2 : ℂ))) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1))
    (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact Fin.rev_lt_rev.mpr hp
  · intro p _
    simp
  · intro p _
    simp
  · intro p hp
    simp only [prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hne : Fin.rev p.2 ≠ Fin.rev p.1 := fun h => (ne_of_lt hp) (Fin.rev_injective h).symm
    have hab : (w (Fin.rev p.2) : ℂ) ≠ (w (Fin.rev p.1) : ℂ) :=
      fun h => hne (hinj (Units.val_injective h))
    have ha : (w (Fin.rev p.2) : ℂ) ≠ 0 := Units.ne_zero _
    have hb : (w (Fin.rev p.1) : ℂ) ≠ 0 := Units.ne_zero _
    simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj (hw _), ← Complex.inv_eq_conj (hw _)]
    generalize (w (Fin.rev p.2) : ℂ) = a at *
    generalize (w (Fin.rev p.1) : ℂ) = b at *
    have h1 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have h2 : a⁻¹ - b⁻¹ ≠ 0 := by
      rw [inv_sub_inv ha hb]
      exact div_ne_zero h1 (mul_ne_zero ha hb)
    rw [div_eq_div_iff h1 h2]
    field_simp

/- English proof (translation)
Introduce `hR n t l z hinj hz`. Rewrite using `[hR n t _ z hinj, hR n t l z hinj, map_sum]`. Use `(Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ ?_).symm` and prove the remaining obligations. Introduce `σ`. Establish `hw : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1` using `fun i => hz _`.

Establish `hi : Function.Injective (z ∘ σ)` using `hinj.comp σ.injective`. Establish `h1` using `mono_term l (z ∘ σ) hw`. Establish `h2` using `pair_term t (z ∘ σ) hi hw`. Rewrite using `[map_mul]`. Simplify using `only [Function.comp_apply] at h2`.

Rewrite using `[← h1, ← h2]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Gen.rConj_pf :
    UpperTheory.Gal.Gen.RFormula → UpperTheory.Gal.Gen.RConj := by
  intro hR n t l z hinj hz
  rw [hR n t _ z hinj, hR n t l z hinj, map_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ ?_).symm
  intro σ
  have hw : ∀ i, ‖((z ∘ σ) i : ℂ)‖ = 1 := fun i => hz _
  have hi : Function.Injective (z ∘ σ) := hinj.comp σ.injective
  have h1 := mono_term l (z ∘ σ) hw
  have h2 := pair_term t (z ∘ σ) hi hw
  rw [map_mul]
  simp only [Function.comp_apply] at h2
  rw [← h1, ← h2]
  rfl
