import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Introduce `K K' d φ _ B ψ hψ hσ hsep`. Take `⟨e, he⟩` from `exists_basis_pow_of_separable K B hsep`. Establish `hP : aeval B.g B.P = 0`. Establish `h1` using `LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)`. Establish `h2 : aeval (LinearMap.mulLeft K.E B.g) B.P = Algebra.lmul K.E B.A (aeval B.g B.P)`.

Rewrite using `[← Polynomial.aeval_algHom_apply]`. Both sides reduce to the same expression. Establish `h3` using `congrArg (fun f : Module.End K.E B.A => f 1) (h2.symm.trans h1)`. Simplify using `using h3`. Use `set B' := overExt φ B ψ hψ hσ with hB'`.

Establish `hg : B'.g = B.g` using `rfl`. Establish `hmap : ∀ x : K'.E, algebraMap K'.E B'.A x = ψ x` using `fun x => rfl`. Establish `hint : IsIntegral K'.E B'.g` using `Algebra.IsIntegral.isIntegral _`. Establish `htop : Algebra.adjoin K'.E {B'.g} = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations.

Establish `hy : (y : B.A) = ∑ i, (e.repr y i) • e i` using `(e.sum_repr y).symm`. Express the relevant statement in the definitionally equal form `(y : B'.A) ∈ Algebra.adjoin K'.E {B'.g}`. Establish `: (y : B'.A) = ∑ i, algebraMap K'.E B'.A (φ (e.repr y i)) * B'.g ^ (i : ℕ)`. Use `hy.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hmap, hψ, he, Algebra.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)`. Set `pb` to `PowerBasis.ofAdjoinEqTop hint htop`. Establish `hchar : B'.P = minpoly K'.E B'.g`.

Establish `h1` using `charpoly_leftMulMatrix pb`. Rewrite `h1` using `[PowerBasis.ofAdjoinEqTop_gen]`. Rewrite using `[← h1, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]`. Both sides reduce to the same expression. Establish `hdvd : minpoly K'.E B'.g ∣ B.P.map φ`.

Use `minpoly.dvd _ _ ?_` and prove the remaining obligations. Rewrite using `[aeval_def, eval₂_map]`. Establish `: (algebraMap K'.E B'.A).comp φ = algebraMap K.E B.A` using `RingHom.ext fun x => hψ x`. Rewrite using `[this]`. Conclude with `hP`.

Rewrite using `[hchar]`. Conclude with `(hsep.map).of_dvd hdvd`.
-/
theorem charpoly_overExt_separable : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e)
      (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)), B.P.Separable → (overExt φ B ψ hψ hσ).P.Separable := by
  intro K K' d φ _ B ψ hψ hσ hsep

  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hsep

  have hP : aeval B.g B.P = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
    have h2 : aeval (LinearMap.mulLeft K.E B.g) B.P = Algebra.lmul K.E B.A (aeval B.g B.P) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    have h3 := congrArg (fun f : Module.End K.E B.A => f 1) (h2.symm.trans h1)
    simpa using h3
  set B' := overExt φ B ψ hψ hσ with hB'
  have hg : B'.g = B.g := rfl
  have hmap : ∀ x : K'.E, algebraMap K'.E B'.A x = ψ x := fun x => rfl
  have hint : IsIntegral K'.E B'.g := Algebra.IsIntegral.isIntegral _

  have htop : Algebra.adjoin K'.E {B'.g} = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : (y : B.A) = ∑ i, (e.repr y i) • e i := (e.sum_repr y).symm
    change (y : B'.A) ∈ Algebra.adjoin K'.E {B'.g}
    have : (y : B'.A) = ∑ i, algebraMap K'.E B'.A (φ (e.repr y i)) * B'.g ^ (i : ℕ) := by
      refine hy.trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [hmap, hψ, he, Algebra.smul_def]; rfl
    rw [this]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hchar : B'.P = minpoly K'.E B'.g := by
    have h1 := charpoly_leftMulMatrix pb
    rw [PowerBasis.ofAdjoinEqTop_gen] at h1
    rw [← h1, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    rfl
  have hdvd : minpoly K'.E B'.g ∣ B.P.map φ := by
    refine minpoly.dvd _ _ ?_
    rw [aeval_def, eval₂_map]
    have : (algebraMap K'.E B'.A).comp φ = algebraMap K.E B.A := RingHom.ext fun x => hψ x
    rw [this]
    exact hP
  rw [hchar]
  exact (hsep.map).of_dvd hdvd

end GlobalTheory.UnitLemma.Unr
