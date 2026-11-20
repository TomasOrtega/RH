import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeKrullDimLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentAverage
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointEquiv (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (Matrix.toLinearEquiv' h.mat.transpose
      (Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem HermNorm.pointEquiv_apply (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl

/- English proof (translation)
Set `E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)` to `h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm`. Set `F` to `LinearMap.toContinuousLinearMap E.symm.toLinearMap`. Use `measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_` and prove the remaining obligations. Simplify using `[F]`. Conclude with `le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))`.
-/
theorem hausdorffMeasure_pointOf_preimage_null (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))

/- English proof (translation)
Simplify using `[frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]`.
-/
theorem frameDeriv_basisFun (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by
  simp [frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]

/- English proof (translation)
Use `set x := h.pointOf y with hx`. Set `a : Matrix {j // j ∉ I₀} (Fin n) ℂ` to `Matrix.of fun k j => eval x (pderiv j (f k))`. Establish `hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap`. Use extensionality with `v`. Simplify using `only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use function extensionality and compare the values at `k`. Simplify `hv (f k) (hf k)` using `[Matrix.mulVec, dotProduct, a]`. Introduce `hv q hq`.

Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)`. Establish `hq0 : eval x q = 0` using `hy q hq`. Establish `hf0 : ∀ k, eval x (f k) = 0` using `fun k => hy _ (hf k)`. Establish `hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j`. Introduce `j`.

Use `congrArg (fun P => eval x (pderiv j P)) hc` as an intermediate fact. Simplify using `only [map_sum, pderiv_mul, map_add, map_mul, hq0, hf0, mul_zero, zero_add] at this`. Simplify `this.symm` using `[a, mul_comm]`. Establish `hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0` using `fun k => by`. Simplify `congrFun hv k` using `[Matrix.mulVec, dotProduct]`.

Establish `: eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0`. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[← mul_assoc, hder, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]`.

Conclude with `(mul_eq_zero.1 this).resolve_left hsy`. Set `M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ` to `Matrix.of fun k j => a k j`. Establish `hM : IsUnit M`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Use `hD using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[frameJacobianDet, RingHom.map_det]`. Use `congr 1`. Use extensionality with `k j`. Simplify using `[M, a, frameDeriv_basisFun]`. Establish `hsurj : Function.Surjective a.mulVecLin`.

Introduce `t`. Take `⟨v, hv⟩` from `Matrix.mulVec_surjective_iff_isUnit.2 hM t`. Use `⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv]`. Use function extensionality and compare the values at `k`.

Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by`. Simplify using `only [Finset.mem_compl, not_not] at hj`. Simplify using `[hj]),`. Use the proof step `Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[j.2]`. Establish `hrank` using `LinearMap.finrank_range_add_finrank_ker a.mulVecLin`. Rewrite `hrank` using `[LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]`. Rewrite using `[hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]`.

Establish `hle : I₀.card ≤ n` using `by simpa using Finset.card_le_univ I₀`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_coneTangent_of_jacobian (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc
        simp only [map_sum, pderiv_mul, map_add, map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega

/- English proof (translation)
Introduce `n m h J hJ hm hmn hfin`. Use `hJ.isPrime` as an intermediate fact. Rewrite using `[ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]`. Break down `(hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq` into its components or cases. Use `measure_mono_null (fun y hy => ?_) (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))` and prove the remaining obligations.

Conclude with `fun q hq => (Classical.not_imp.1 hy).1 q hq`. Take `⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩` from `hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ) set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f`. Establish `hsD : s * D ∉ J` using `fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ`. Establish `hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D})) (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})), Ideal.map_span, Set.image_singleton]`.

Establish `hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J)` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz`. Rewrite `h1` using `[heq]`. Assume the negation of the conclusion as `hge`. Establish `h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1` using `by gcongr; exact not_lt.1 hge`.

Establish `h3` using `h2.trans h1`. Conclude with `absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))`. Use `measure_mono_null (fun y hy => ?_) (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))` and prove the remaining obligations. Take `⟨hyC, hyT⟩` from `Classical.not_imp.1 hy`. Establish `hsD0 : eval (h.pointOf y) (s * D) = 0`.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[map_mul]`. Conclude with `hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))`. Introduce `q hq`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hq`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Express the relevant statement in the definitionally equal form `eval (h.pointOf y) (a + c * (s * D)) = 0`. Rewrite using `[map_add, map_mul, hsD0, mul_zero, add_zero]`. Conclude with `hyC a ha`.
-/
theorem ConeTangentDim.proof (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by
  intro n m h J hJ hm hmn hfin
  have := hJ.isPrime
  rw [ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]
  rcases (hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq
  · refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))
    exact fun q hq => (Classical.not_imp.1 hy).1 q hq
  · obtain ⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩ :=
      hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ)
    set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f
    have hsD : s * D ∉ J := fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ
    have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m := by
      rw [← ringKrullDim_eq_of_ringEquiv
          (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D}))
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})),
        Ideal.map_span, Set.image_singleton]
      have hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
        mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [heq] at h1
      by_contra hge
      have h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤
          ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1 := by
        gcongr; exact not_lt.1 hge
      have h3 := h2.trans h1
      exact absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))
    refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))
    obtain ⟨hyC, hyT⟩ := Classical.not_imp.1 hy
    have hsD0 : eval (h.pointOf y) (s * D) = 0 := by
      by_contra hne
      rw [map_mul] at hne
      exact hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC
        (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    change eval (h.pointOf y) (a + c * (s * D)) = 0
    rw [map_add, map_mul, hsD0, mul_zero, add_zero]
    exact hyC a ha

end

end GroundTheory.Heights₂.Heights
