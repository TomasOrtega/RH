import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

/- English proof (translation)
Introduce `f N P α hP hc τ i j hij`. Simplify using `only at hij`. Assume the negation of the conclusion as `hne`. Set `w : Fin f → Equiv.Perm (Fin N)` to `Function.update 1 τ (Equiv.swap i j)`. Establish `hsign : blockSign f N w = -1`.

Unfold `blockSign`. Rewrite using `[Finset.prod_eq_single τ]`. Simplify using `[w, Equiv.Perm.sign_swap hne]`. Introduce `b _ hb`. Simplify using `[w, Function.update_of_ne hb]`.

Simplify using the standard rewrite rules. Establish `hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α`. Use extensionality with `⟨σ, k⟩`. Express the relevant statement in the definitionally equal form `α (σ, w σ k) = α (σ, k)`. Distinguish the cases in `hσ : σ = τ`.

Substitute `hσ` using the available equality. Simplify using `only [w, Function.update_self]`. Break down `eq_or_ne k i with rfl | hki` into its components or cases. Rewrite using `[Equiv.swap_apply_left]`. Conclude with `hij.symm`.

Break down `eq_or_ne k j with rfl | hkj` into its components or cases. Rewrite using `[Equiv.swap_apply_right]`. Conclude with `hij`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hki hkj]`. Simplify using `[w, Function.update_of_ne hσ]`.

Establish `key` using `h1 f N w P α`. Rewrite `key` using `[hα, hP w, hsign, coeff_smul]`. Establish `: coeff α P = 0`. Establish `h2 : (2 : ℚ) * coeff α P = 0`. Rewrite `key` using `[smul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `using h2`. Conclude with `hc this`.
-/
theorem FlagAltCoeffInjective.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagAltCoeffInjective.Statement := by
  classical
  intro f N P α hP hc τ i j hij
  simp only at hij
  by_contra hne
  let w : Fin f → Equiv.Perm (Fin N) := Function.update 1 τ (Equiv.swap i j)
  have hsign : blockSign f N w = -1 := by
    unfold blockSign
    rw [Finset.prod_eq_single τ]
    · simp [w, Equiv.Perm.sign_swap hne]
    · intro b _ hb
      simp [w, Function.update_of_ne hb]
    · simp
  have hα : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α := by
    ext ⟨σ, k⟩
    change α (σ, w σ k) = α (σ, k)
    by_cases hσ : σ = τ
    · subst hσ
      simp only [w, Function.update_self]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left]; exact hij.symm
      · rcases eq_or_ne k j with rfl | hkj
        · rw [Equiv.swap_apply_right]; exact hij
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    · simp [w, Function.update_of_ne hσ]
  have key := h1 f N w P α
  rw [hα, hP w, hsign, coeff_smul] at key
  have : coeff α P = 0 := by
    have h2 : (2 : ℚ) * coeff α P = 0 := by
      rw [smul_eq_mul] at key
      linarith
    simpa using h2
  exact hc this

end RestTerms

end GroundTheory.Heights₂.Heights
