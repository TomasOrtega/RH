import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenSpan

noncomputable section

open NumberField InfinitePlace Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def mulVHom {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) where
  toFun := mulV n r v
  map_one' := by simp [mulV]
  map_mul' x y := by simp [mulV, smul_add]

/- English proof (translation)
Introduce `h`. Establish `hn : ∏ i, (InfinitePlace.mk (σs i)) (algebraMap (𝓞 L) L (v : 𝓞 L)) = 1`. Use `congrArg norm h` as an intermediate fact. Rewrite `this` using `[norm_prod, norm_one]`. Simplify `this` using `[InfinitePlace.apply]`.

Set `g : Fin (q + 1) → InfinitePlace L` to `fun i => InfinitePlace.mk (σs i)`. Set `a : InfinitePlace L → ℕ` to `fun w => (Finset.univ.filter fun i => g i = w).card`. Establish `hsum : ∑ w, a w = q + 1`. Use `Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 1)))) (t := (Finset.univ : Finset (InfinitePlace L))) (f := g) (fun _ _ => Finset.mem_univ _)` as an intermediate fact. Simplify `this.symm` using `[a]`.

Establish `hprod : ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1`. Rewrite using `[← hn, ← Finset.prod_fiberwise Finset.univ g]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl (g := fun _ => w (algebraMap (𝓞 L) L (v : 𝓞 L))), Finset.prod_const]`. Introduce `i hi`.

Establish `hgi : g i = w` using `(Finset.mem_filter.mp hi).2`. Simplify using `only [g] at hgi`. Rewrite using `[hgi]`. Conclude with `hv a (by omega) (by omega) hprod`.
-/
theorem prod_emb_ne_one {L : Type} [Field L] [NumberField L] (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1)
    (q : ℕ) (hq : q + 1 ≤ m) (σs : Fin (q + 1) → (L →+* ℂ)) :
    ∏ i, σs i (algebraMap (𝓞 L) L (v : 𝓞 L)) ≠ 1 := by
  classical
  intro h
  have hn : ∏ i, (InfinitePlace.mk (σs i)) (algebraMap (𝓞 L) L (v : 𝓞 L)) = 1 := by
    have := congrArg norm h
    rw [norm_prod, norm_one] at this
    simpa [InfinitePlace.apply] using this
  let g : Fin (q + 1) → InfinitePlace L := fun i => InfinitePlace.mk (σs i)
  let a : InfinitePlace L → ℕ := fun w => (Finset.univ.filter fun i => g i = w).card
  have hsum : ∑ w, a w = q + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 1))))
      (t := (Finset.univ : Finset (InfinitePlace L))) (f := g) (fun _ _ => Finset.mem_univ _)
    simpa [a] using this.symm
  have hprod : ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
    rw [← hn, ← Finset.prod_fiberwise Finset.univ g]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => w (algebraMap (𝓞 L) L (v : 𝓞 L))), Finset.prod_const]
    intro i hi
    have hgi : g i = w := (Finset.mem_filter.mp hi).2
    simp only [g] at hgi
    rw [hgi]
  exact hv a (by omega) (by omega) hprod

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

open PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes in
/- English proof (translation)
Introduce `L _ _ _ m v hv n r q hq`. Set `lam : Fin n × Fin r × (L →+* ℂ) → ℂ` to `fun j => j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L))`. Set `β : Fin n × Fin r × (L →+* ℂ) → Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) → ℂ` to `fun j x => j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1))`. Use `⟨∏ J : Fin (q + 1) → Fin n × Fin r × (L →+* ℂ), gpoly (∏ i, lam (J i)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_prod]`.

Use `Finset.prod_ne_zero_iff.mpr fun J _ => ?_` and prove the remaining obligations. Rewrite using `[gpoly_eval_one, Ne, Complex.normSq_eq_zero, sub_eq_zero]`. Conclude with `fun h => prod_emb_ne_one m v hv q hq (fun i => (J i).2.2) h.symm`. Introduce `α`. Establish `hβ : ∀ j x, β j (Additive.ofMul (mulVHom n r (v : 𝓞 L) x)) = lam j * β j (Additive.ofMul x)`.

Introduce `j x`. Express the relevant statement in the definitionally equal form `j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (mulV n r (v : 𝓞 L) x) j.1 j.2.1)) = j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L)) * j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd x j.1 j.2.1))`. Simplify using `only [mulV, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, map_mul]`. Conclude with `cup_kill (mulVHom n r (v : 𝓞 L)) β lam hβ (fun α => mat_span L n r α) q α`.
-/
theorem PositivityTheory.KB.SplitAffineSpectral.eigen : PositivityTheory.KB.SplitAffineSpectral.Eigen := by
  intro L _ _ _ m v hv n r q hq
  classical
  let lam : Fin n × Fin r × (L →+* ℂ) → ℂ := fun j => j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L))
  let β : Fin n × Fin r × (L →+* ℂ) → Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) → ℂ :=
    fun j x => j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1))
  refine ⟨∏ J : Fin (q + 1) → Fin n × Fin r × (L →+* ℂ), gpoly (∏ i, lam (J i)), ?_, ?_⟩
  · rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun J _ => ?_
    rw [gpoly_eval_one, Ne, Complex.normSq_eq_zero, sub_eq_zero]
    exact fun h => prod_emb_ne_one m v hv q hq (fun i => (J i).2.2) h.symm
  · intro α
    have hβ : ∀ j x, β j (Additive.ofMul (mulVHom n r (v : 𝓞 L) x)) = lam j * β j (Additive.ofMul x) := by
      intro j x
      change j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (mulV n r (v : 𝓞 L) x) j.1 j.2.1)) =
        j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L)) * j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd x j.1 j.2.1))
      simp only [mulV, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, map_mul]
    exact cup_kill (mulVHom n r (v : 𝓞 L)) β lam hβ (fun α => mat_span L n r α) q α
