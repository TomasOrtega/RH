import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CcConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD T σ hσ w hw`. Establish `hτ : IsCC (resQ T.F σ)`. Unfold `IsCC at *`. Conclude with `hσ`. Establish `hconj` using `isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC`.

Establish `hP : D.Psi (resQ T.F σ) = 1`. Take `⟨u, hu⟩` from `isConj_iff.mp hconj`. Rewrite using `[← hD.Psi_even, ← hu]`. Simplify using `only [map_mul, map_inv]`. Rewrite using `[mul_comm, inv_mul_cancel_left]`.

Establish `hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ)`. Establish `: D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ)`. Unfold `Raw.th`. Both sides reduce to the same expression. Rewrite `this` using `[MonoidHom.mul_apply, hP, mul_one]`.

Conclude with `this`. Establish `hrt : (T.fr ∅).rt w σ = 1`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hw`. Break down `hw with rfl | rfl | rfl` into its components or cases. Simplify using `only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]`.

Simplify using `only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one, MonoidHom.coe_comp, Function.comp_apply]`. Unfold `chi`. Apply the tactic sequence `cases T.pr <;> simp [lab, Raw.ps, hth]`. Simplify using `only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, MonoidHom.coe_comp, Function.comp_apply]`. Unfold `chi`.

Apply the tactic sequence `cases T.pr <;> simp [lab, Raw.ps, hth]`. Use `show (Units.map _) ((T.fr ∅).rt w σ) = 1`. Rewrite using `[hrt, map_one]`.
-/
theorem UpperTheory.V.Ws.residualCharacter_complexConjugation_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (σ : G T.F Ω), IsCC σ → ∀ w ∈ [0, wPs, -wPs], T.rbU w σ = 1 := by
  intro Ω _ _ _ l _ c D hD T σ hσ w hw
  have hτ : IsCC (resQ T.F σ) := by
    unfold IsCC at *
    exact hσ
  have hconj := isConj_of_isComplexConjugation Ω (resQ T.F σ) D.cc hτ hD.isCC
  have hP : D.Psi (resQ T.F σ) = 1 := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hconj
    rw [← hD.Psi_even, ← hu]
    simp only [map_mul, map_inv]
    rw [mul_comm, inv_mul_cancel_left]
  have hth : D.th (AlgEquiv.restrictScalars ℚ σ) = D.al (AlgEquiv.restrictScalars ℚ σ) := by
    have : D.th (resQ T.F σ) = (D.al * D.Psi) (resQ T.F σ) := by
      unfold Raw.th
      rfl
    rw [MonoidHom.mul_apply, hP, mul_one] at this
    exact this
  have hrt : (T.fr ∅).rt w σ = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · simp only [Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_zero, Prod.snd_zero, zpow_zero, mul_one]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_zero, one_mul, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
    · simp only [Fr.rt, Tower.fr, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one,
        MonoidHom.coe_comp, Function.comp_apply]
      unfold chi
      cases T.pr <;> simp [lab, Raw.ps, hth]
  show (Units.map _) ((T.fr ∅).rt w σ) = 1
  rw [hrt, map_one]
