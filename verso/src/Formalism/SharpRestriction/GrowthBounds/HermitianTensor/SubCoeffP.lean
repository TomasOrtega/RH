import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.RowActTransv
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamAddC

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

/- English proof (translation)
Introduce `K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht`. Establish `hsv` using `fun u => subCoeffP K r ν v hv u`. Establish `hst` using `fun u => subCoeffP K r ν' t ht u`. Take `⟨hvw, hvi⟩` from `mem_dualWeyl_iff.mp hv`. Take `⟨htw, hti⟩` from `mem_dualWeyl_iff.mp ht`.

Use `set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF`. Establish `hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 → scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F`. Introduce `t0 c hc`. Break down `midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩` into its components or cases. Rewrite using `[hνpm j]`.

Conclude with `lam_scaleM L N _ _ hPh j c hc v t hsv hst`. Rewrite using `[lam_scaleN L t0 hn c ν ν' v t hvw htw]`. Substitute `h0` using the available equality. Rewrite using `[hνp0]`. Rewrite using `[lam_scaleN L t0 hn c ν ν' v t hvw htw]`.

Substitute `hl` using the available equality. Rewrite using `[hνl, hν'l, hνpl]`. Establish `hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F`. Introduce `l j hlj c`. Break down `midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩` into its components or cases.

Break down `midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩` into its components or cases. Establish `hne : l' ≠ j'`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hlj`. Conclude with `lam_addM L N _ _ hPh l' j' hne c v t hsv hst`.

Substitute `h0'` using the available equality. Conclude with `lam_addC L j' c v t hvi hti`. Substitute `hl'` using the available equality. Conclude with `absurd hlj (not_lt.mpr (Fin.le_last _))`. Substitute `h0` using the available equality.

Conclude with `absurd hlj (Fin.not_lt_zero _)`. Substitute `hl` using the available equality. Apply `colAdd_trivial` to reduce the goal to its premises. Introduce `m hm`. Rewrite using `[wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]`.

Rewrite using `[mem_dualWeyl_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Use function extensionality and compare the values at `t0`. Conclude with `wt_of_scale t0 (νp t0) F (hscale t0) m hm`.

Introduce `l j hlj`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Establish `h1` using `congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)`. Simplify using `only [AlgHom.comp_apply, hcol l j hlj] at h1`.

Simplify `h1` using `[MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval]`.
-/
theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

/- English proof (translation)
The claim follows from `QB.subCoeffP`.
-/
theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end
