import Development.EtaleCohomology.EtaleTrace.PNBasicPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `ha`. Apply `HomogeneousLocalization.val_injective` to reduce the goal to its premises. Establish `h : a.val ^ n = 0`. Rewrite using `[← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]`.

Rewrite using `[HomogeneousLocalization.val_zero]`. Conclude with `IsReduced.eq_zero _ ⟨n, h⟩`.
-/
theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

/- English proof (translation)
Establish `: ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x)`. Introduce `x`. Use `haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime`. Use `haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal`. Set `e` to `Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x`.

Conclude with `isReduced_of_injective e.toRingHom e.injective`. Conclude with `isReduced_of_isReduced_stalk _`.
-/
theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

/- English proof (translation)
Introduce `h`. Establish `hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)`. Rewrite using `[HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]`. Conclude with `DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)`. Establish `h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal` using `h hm`.

Rewrite `h2` using `[HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]`. Conclude with `X_ne_zero _ h2`.
-/
theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

/- English proof (translation)
Rewrite using `[irreducibleSpace_def]`. Establish `: (Set.univ : Set (PN k d)) = closure {gen k d}`. Use extensionality with `y`. Simplify using `only [Set.mem_univ, true_iff]`. Conclude with `(ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1 (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)`.

Express the relevant statement in the definitionally equal form `IsIrreducible (Set.univ : Set (PN k d))`. Rewrite using `[this]`. Conclude with `isIrreducible_singleton.closure`.
-/
theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

/- English proof (translation)
Introduce `k _ d` and use `by haveI := pn_reduced k d haveI := pn_irred k d exact isIntegral_of_irreducibleSpace_of_isReduced _`.
-/
theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
