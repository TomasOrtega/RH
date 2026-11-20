import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GalSplit
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

open NumberField GroundTheory.Global.InfinitePlace
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ hσ m hm`. Use `⟨fun hF => ?_, fun p => ?_⟩` and prove the remaining obligations. Establish `h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion)` using `fun v => by haveI : IsAlgClosed v.Completion := IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm`. Conclude with `⟨IsAlgClosed.lift⟩`. Conclude with `⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩`.

Take `⟨e, he, hs⟩` from `UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E) (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p`. Establish `hd : ∀ r i, e (infiniteAdeleRingMap (K` using `F) (L := E) r) i = r := fun r i => by`. Use `he 1 r i` as an intermediate fact. Rewrite `this` using `[tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul]`. Then use the resulting hypothesis. Establish `hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x)` using `fun x i => by`.

Use `he x 1 i` as an intermediate fact. Rewrite `this` using `[tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one]`. Then use the resulting hypothesis. Use `⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩` and prove the remaining obligations. Set `b` to `Module.finBasis F E`. Establish `h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y` using `fun y i => by conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]`.

Rewrite using `[map_sum, map_sum, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun j _ => he _ _ _`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Repeatedly rewrite using `[h]`. Conclude with `continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)`.

Establish `h : ∀ a, e.symm a = ∑ i, infiniteAdeleRingMap (K` using `F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by`. Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Rewrite using `[map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]`. Repeatedly rewrite using `[map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]`.

Rewrite using `[Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj.symm, mul_zero]`. Simplify using the standard rewrite rules.

Establish `h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K` using `F) (L := E) (a i) * e.symm (Pi.single i 1) :=`. Use function extensionality and compare the values at `h`. Rewrite using `[h']`. Conclude with `continuous_finsetSum _ fun i _ => (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const`.
-/
theorem UpperTheory.ConvolutionTheory.L1.infSplit :
    UpperTheory.ConvolutionTheory.L1.InfSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm
  refine ⟨fun hF => ?_, fun p => ?_⟩
  · have h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion) := fun v => by
      haveI : IsAlgClosed v.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm
      exact ⟨IsAlgClosed.lift⟩
    exact ⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩
  · obtain ⟨e, he, hs⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E)
      (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p
    have hd : ∀ r i, e (infiniteAdeleRingMap (K := F) (L := E) r) i = r := fun r i => by
      have := he 1 r i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul] at this
    have hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x) := fun x i => by
      have := he x 1 i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one] at this
    refine ⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩
    · let b := Module.finBasis F E
      have h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y := fun y i => by
        conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]
        rw [map_sum, map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => he _ _ _
      refine continuous_pi fun i => ?_
      simp_rw [h]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)
    · have h : ∀ a, e.symm a =
          ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by
        apply e.injective
        funext k
        rw [map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]
        simp_rw [map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj.symm, mul_zero]
        · simp
      have h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) :=
        funext h
      rw [h']
      exact continuous_finsetSum _ fun i _ =>
        (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const
