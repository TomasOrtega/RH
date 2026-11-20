import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Establish `hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n))` using `IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)`. Establish `h` using `(MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj`. Establish `hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) = genPar k e n`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]`.

Rewrite `h` using `[hc]`. Then use the resulting hypothesis.
-/
theorem genPar_algebraicIndependent (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k)
      (GenParField k e n)) :=
    IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)
  have h := (MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj
  have hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) =
      genPar k e n := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]
  rwa [hc] at h

/- English proof (translation)
Establish `h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X)` using `rfl`. Rewrite using `[h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]`. Conclude with `Ideal.Quotient.mkₐ_surjective E _`.
-/
theorem secCoord_adjoin {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

/- English proof (translation)
Establish `h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]`. Conclude with `Ideal.mem_sup_right (Ideal.subset_span rfl)`. Rewrite using `[← h, chartForm, linForm, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem secCoord_chart {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : ∑ j, algebraMap E (SecAlg Q y) (y (.inr j)) * secCoord Q y j = 1 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (chartForm y) = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  rw [← h, chartForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

/- English proof (translation)
Introduce `k _ _ n e Q g hQ hg`. Establish `hfin` using `h₁ k (GenParField k e n) n e Q g (genPar k e n) (genPar_algebraicIndependent k e n) hQ hg`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Use `h₂ k n e Q g hQ hg` as an intermediate fact. Use `h₃ k n e Q g hQ hg` as an intermediate fact.

Establish `hirr` using `h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j)) (secCoord_adjoin _ _) (secCoord_chart _ _)`. Take `⟨m, -, hm⟩` from `h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg`. Establish `hd` using `h₇ (GenParField k e n) (GenSec k e Q) n _ ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])`. Rewrite `hd` using `[← pow_mul]`. Take `⟨u, hu⟩` from `hirr.prime.dvd_of_dvd_pow hd`.

Break down `(h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'` into its components or cases. Conclude with `absurd hN hirr.not_isUnit`. Take `⟨c, hc, rfl⟩` from `(MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'`. Conclude with `⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩`.
-/
theorem ChowNormFormGeneric.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : GenSecSeparable.Statement) (h₄ : ChowSecDvd.Statement)
    (h₅ : NormFormIrreducible.Statement) (h₆ : GenChowIrreducible.Statement)
    (h₇ : NormFormDvd.Statement) : ChowNormFormGeneric.Statement := by
  intro k _ _ n e Q g hQ hg
  have hfin := h₁ k (GenParField k e n) n e Q g (genPar k e n)
    (genPar_algebraicIndependent k e n) hQ hg
  refine ⟨hfin, ?_⟩
  have := h₂ k n e Q g hQ hg
  have := h₃ k n e Q g hQ hg
  have hirr := h₅ (GenParField k e n) (GenSec k e Q) n _ (fun j => genPar k e n (.inr j))
    (secCoord_adjoin _ _) (secCoord_chart _ _)
  obtain ⟨m, -, hm⟩ := h₄ k (GenParField k e n) n e Q g (genPar k e n) hQ hg
  have hd := h₇ (GenParField k e n) (GenSec k e Q) n _
    ((specRest (algebraMap k (GenParField k e n)) g (genPar k e n)) ^ m) (by rwa [map_pow])
  rw [← pow_mul] at hd
  obtain ⟨u, hu⟩ := hirr.prime.dvd_of_dvd_pow hd
  rcases (h₆ k n e Q g hQ hg).isUnit_or_isUnit hu with hN | hu'
  · exact absurd hN hirr.not_isUnit
  obtain ⟨c, hc, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp hu'
  exact ⟨c, hc.ne_zero, by rw [hu, mul_comm]⟩

end

end GroundTheory.Heights₂.Heights.Vertical
