import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma kExp_Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

section L2
open scoped Matrix.Norms.L2Operator

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Establish `hfin` using `Matrix.finite_spectrum k`. Establish `hN : IsStarNormal k` using `⟨by`. Rewrite using `[Commute, SemiconjBy, Unitary.star_mul_self_of_mem hu, Unitary.mul_star_self_of_mem hu]⟩`. Establish `hcl : ContinuousOn Complex.log (spectrum ℂ k)` using `hfin.continuousOn _`.

Establish `hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1` using `fun z hz => by`. Simplify using `using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hz`. Establish `hJ : Commute k (Jm ε)` using `hc`. Establish `hJs : Commute (star k) (Jm ε)`. Establish `h` using `congrArg star hc`.

Simplify using `only [star_mul, Matrix.star_eq_conjTranspose, kExp_Jm_conjTranspose] at h`. Conclude with `h.symm`. Establish `hZJ : Commute (cfc Complex.log k) (Jm ε)` using `Commute.cfc hJ hJs _`. Establish `hstar : star (cfc Complex.log k) = -cfc Complex.log k`. Rewrite using `[← cfc_star, ← cfc_neg]`.

Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Establish `h1` using `hcirc z hz`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.log_re, h1]`. Use `⟨cfc Complex.log k, ⟨?_, hZJ.eq⟩, ?_⟩` and prove the remaining obligations. Unfold `inG`.

Rewrite using `[← Matrix.star_eq_conjTranspose, hstar, neg_mul, hZJ.eq]`. Conclude with `neg_add_cancel _`. Rewrite using `[← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc Complex.log k) (cfc_predicate _ _), ← cfc_comp NormedSpace.exp Complex.log k hN ((hfin.image _).continuousOn _) hcl] conv_rhs => rw [← cfc_id ℂ k hN]`. Use `cfc_congr fun z hz => ?_` and prove the remaining obligations. Establish `hz0 : z ≠ 0`.

Introduce `h`. Establish `h1` using `hcirc z hz`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`. Simplify using `only [Function.comp_apply, id]`.

Rewrite using `[← Complex.exp_eq_exp_ℂ, Complex.exp_log hz0]`.
-/
lemma exists_inK_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k := by
  obtain ⟨hu, hc⟩ := hk
  have hfin := Matrix.finite_spectrum k
  have hN : IsStarNormal k := ⟨by
    rw [Commute, SemiconjBy, Unitary.star_mul_self_of_mem hu, Unitary.mul_star_self_of_mem hu]⟩
  have hcl : ContinuousOn Complex.log (spectrum ℂ k) := hfin.continuousOn _

  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hz

  have hJ : Commute k (Jm ε) := hc
  have hJs : Commute (star k) (Jm ε) := by
    have h := congrArg star hc
    simp only [star_mul, Matrix.star_eq_conjTranspose, kExp_Jm_conjTranspose] at h
    exact h.symm
  have hZJ : Commute (cfc Complex.log k) (Jm ε) := Commute.cfc hJ hJs _
  have hstar : star (cfc Complex.log k) = -cfc Complex.log k := by
    rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, h1]
  refine ⟨cfc Complex.log k, ⟨?_, hZJ.eq⟩, ?_⟩
  · unfold inG
    rw [← Matrix.star_eq_conjTranspose, hstar, neg_mul, hZJ.eq]
    exact neg_add_cancel _
  · rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (a := cfc Complex.log k) (cfc_predicate _ _),
      ← cfc_comp NormedSpace.exp Complex.log k hN ((hfin.image _).continuousOn _) hcl]
    conv_rhs => rw [← cfc_id ℂ k hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h
      have h1 := hcirc z hz
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    simp only [Function.comp_apply, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log hz0]

end L2

/- English proof (translation)
The claim follows from `exists_inK_exp_eq_of_mem_Kset hk`.
-/
theorem exists_exp_eq_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : ∃ Z, inK ε Z ∧ NormedSpace.exp Z = k :=
  exists_inK_exp_eq_of_mem_Kset hk

end ReciprocityTheory.ChartRestriction.DS
