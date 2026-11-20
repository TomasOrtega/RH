import Formalism.WachLatticeTwists.HodgeTateChains.AdicPerturbationFixedFreeAndCoboundary
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.TwistKill
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Introduce `ℓ _ R _ _ Xm _ _ _ _ ϖ z z' hzz hc hz g B hinj hsur`. Take `⟨S, hS1, hS2⟩` from `inverse_operator_from_injectivity R Xm g z hinj hsur`. Take `⟨h1, _, h3⟩` from `t3 R Xm ϖ z hc hz g S B hS1 hS2`. Use `⟨h1, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h3 (z' • x)`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, smul_smul, hzz, algebraMap_smul]`.
-/
theorem unit_congruence_gives_perturbation : AdicPerturbationFixedFreeAndCoboundary := by
  intro ℓ _ R _ _ Xm _ _ _ _ ϖ z z' hzz hc hz g B hinj hsur
  obtain ⟨S, hS1, hS2⟩ := inverse_operator_from_injectivity R Xm g z hinj hsur
  obtain ⟨h1, _, h3⟩ := t3 R Xm ϖ z hc hz g S B hS1 hS2
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨y, hy⟩ := h3 (z' • x)
  refine ⟨y, ?_⟩
  rw [← hy, smul_smul, hzz, algebraMap_smul]

/- English proof (translation)
Introduce `O _ _ hO HT HD' HV HV' _ _ _ _ _ _ _ _ _ _ _ _ jT pr pair pT Hf Hf' hann hcomp a`. Rewrite using `[← bkSubspace O (FractionRing O) hO HV HV' pair Hf Hf' hann (jT a)]`. Use `forall₂_congr fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hcomp, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]`. Both sides reduce to the same expression.
-/
theorem bkb : StatBKb := by
  intro O _ _ hO HT HD' HV HV' _ _ _ _ _ _ _ _ _ _ _ _ jT pr pair pT Hf Hf' hann hcomp a
  rw [← bkSubspace O (FractionRing O) hO HV HV' pair Hf Hf' hann (jT a)]
  refine forall₂_congr fun b _ => ?_
  rw [hcomp, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  rfl

/- English proof (translation)
Introduce `ℓ _ w m hm h2 hw U h0U hne D hP hUn hFl hLES hInv O _ _ _ d _ N φ`. Establish `hk` using `h0 ℓ w m hm h2 hw U h0U hne D hP hUn hFl hLES hInv`. Apply `Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O d N ℓ (c0 ℓ m U)` to reduce the goal to its premises. Introduce `x hx`. Establish `h1 : (ℓ ^ c0 ℓ m U) • φ.symm ⟨x, hx⟩ = 0`.

Use `hk (φ.symm ⟨x, hx⟩)` as an intermediate fact. Rewrite `this` using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `this`. Establish `h3 : (ℓ ^ c0 ℓ m U) • (⟨x, hx⟩ : N) = 0`. Use `congrArg φ h1` as an intermediate fact.

Rewrite `this` using `[map_nsmul, AddEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis. Establish `h4 : (ℓ ^ c0 ℓ m U) • x = 0` using `congrArg Subtype.val h3`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Conclude with `h4`.
-/
theorem H0_length_bound_holds : InvariantsLengthBound := by
  intro ℓ _ w m hm h2 hw U h0U hne D hP hUn hFl hLES hInv O _ _ _ d _ N φ
  have hk := h0 ℓ w m hm h2 hw U h0U hne D hP hUn hFl hLES hInv
  apply Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O d N ℓ (c0 ℓ m U)
  intro x hx
  have h1 : (ℓ ^ c0 ℓ m U) • φ.symm ⟨x, hx⟩ = 0 := by
    have := hk (φ.symm ⟨x, hx⟩)
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  have h3 : (ℓ ^ c0 ℓ m U) • (⟨x, hx⟩ : N) = 0 := by
    have := congrArg φ h1
    rwa [map_nsmul, AddEquiv.apply_symm_apply, map_zero] at this
  have h4 : (ℓ ^ c0 ℓ m U) • x = 0 := congrArg Subtype.val h3
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact h4

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
