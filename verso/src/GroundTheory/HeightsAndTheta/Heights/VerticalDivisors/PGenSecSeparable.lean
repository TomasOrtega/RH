import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChartPointTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenSecSeparable

/- English proof (translation)
Establish `hinj : Function.Injective (IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n))` using `IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n)`. Establish `h` using `(MvPolynomial.algebraicIndependent_X (Par e n) k).map' hinj`. Establish `hc : (⇑(IsScalarTower.toAlgHom k (MvPolynomial (Par e n) k) (GenParField k e n)) ∘ X) = genPar k e n`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, IsScalarTower.coe_toAlgHom', genPar]`.

Rewrite `h` using `[hc]`. Then use the resulting hypothesis.
-/
theorem genPar_algIndep (k : Type*) [Field k] (e n : ℕ) :
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
theorem adjoin_secCoord {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) : Algebra.adjoin E (Set.range (secCoord Q y)) = ⊤ := by
  have h : Set.range (secCoord Q y) = Set.range (Ideal.Quotient.mkₐ E (secIdeal Q y) ∘ X) := rfl
  rw [h, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
    AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective E _

/- English proof (translation)
Establish `h : Ideal.Quotient.mk (secIdeal Q y) (secForm y i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))`. Rewrite using `[← h, secForm, linForm, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem secCoord_form {E : Type*} [Field E] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) E))
    (y : Par e n → E) (i : Fin e) :
    ∑ j, algebraMap E (SecAlg Q y) (y (.inl (i, j))) * secCoord Q y j = 0 := by
  have h : Ideal.Quotient.mk (secIdeal Q y) (secForm y i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
  rw [← h, secForm, linForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  rfl

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
Use `set I := secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)`. Establish `key : ((aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)) : MvPolynomial (Fin n) k →ₐ[k] GenSec k e Q) : MvPolynomial (Fin n) k →+* _) = (Ideal.Quotient.mk I).comp (MvPolynomial.map (algebraMap k (GenParField k e n)))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.coe_coe, aeval_C, RingHom.coe_comp, Function.comp_apply, map_C]`.

Rewrite using `[IsScalarTower.algebraMap_apply k (GenParField k e n) (GenSec k e Q)]`. Both sides reduce to the same expression. Introduce `j`. Simplify using `only [RingHom.coe_coe, aeval_X, RingHom.coe_comp, Function.comp_apply, map_X]`. Both sides reduce to the same expression.

Establish `h` using `congrArg (fun φ => φ f) key`. Simplify using `only [RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply] at h`. Rewrite using `[h, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))`.
-/
theorem aeval_secCoord (k : Type*) [Field k] (e : ℕ) {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k))
    (f : MvPolynomial (Fin n) k) (hf : f ∈ Q) :
    aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)) f = 0 := by
  set I := secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)
  have key : ((aeval (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n)) : MvPolynomial (Fin n) k →ₐ[k] GenSec k e Q) : MvPolynomial (Fin n) k →+* _) =
      (Ideal.Quotient.mk I).comp (MvPolynomial.map (algebraMap k (GenParField k e n))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_coe, aeval_C, RingHom.coe_comp, Function.comp_apply, map_C]
      rw [IsScalarTower.algebraMap_apply k (GenParField k e n) (GenSec k e Q)]
      rfl
    · intro j
      simp only [RingHom.coe_coe, aeval_X, RingHom.coe_comp, Function.comp_apply, map_X]
      rfl
  have h := congrArg (fun φ => φ f) key
  simp only [RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply] at h
  rw [h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

end GenSecSeparable

open GenSecSeparable in
/- English proof (translation)
Introduce `k _ _ n e Q g hQ hg`. Establish `: Module.Finite (GenParField k e n) (GenSec k e Q)` using `h₁ k (GenParField k e n) n e Q g (genPar k e n) (genPar_algIndep k e n) hQ hg`. Establish `: IsDomain (GenSec k e Q)` using `h₂ k n e Q g hQ hg`. Set `: Field (GenSec k e Q)` to `(isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)).toField`. Conclude with `h₄ k n e (GenSec k e Q) _ (adjoin_secCoord _ _) (secCoord_form _ _) (secCoord_chart _ _) fun j₀ hj₀ => h₃ k (GenSec k e Q) n e Q g hQ hg _ j₀ (aeval_secCoord k e Q) hj₀`.
-/
theorem GenSecSeparable.proof (h₁ : SecAlgFinite.Statement) (h₂ : GenSecDomain.Statement)
    (h₃ : ChartPointTrdeg.Statement) (h₄ : SecPointSeparable.Statement) :
    GenSecSeparable.Statement := by
  intro k _ _ n e Q g hQ hg
  have : Module.Finite (GenParField k e n) (GenSec k e Q) :=
    h₁ k (GenParField k e n) n e Q g (genPar k e n) (genPar_algIndep k e n) hQ hg
  have : IsDomain (GenSec k e Q) := h₂ k n e Q g hQ hg
  let : Field (GenSec k e Q) :=
    (isField_of_isIntegral_of_isField' (R := GenParField k e n) (Field.toIsField _)).toField
  exact h₄ k n e (GenSec k e Q) _ (adjoin_secCoord _ _) (secCoord_form _ _) (secCoord_chart _ _)
    fun j₀ hj₀ => h₃ k (GenSec k e Q) n e Q g hQ hg _ j₀ (aeval_secCoord k e Q) hj₀

end

end GroundTheory.Heights₂.Heights.Vertical
