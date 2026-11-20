import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsRelevant)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

noncomputable section

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type}

/- English proof (translation)
Establish `h : (segreLiftMap ι F W).comp (segreIncl ι F) = (IsScalarTower.toAlgHom F (MRing ι F ⧸ W) (Polynomial (MRing ι F ⧸ W))).comp (Ideal.Quotient.mkₐ F W)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[segreIncl, segreLiftMap, segreLiftVal]`. Simplify using `using DFunLike.congr_fun h s`.
-/
theorem segreLiftMap_segreIncl (W : Ideal (MRing ι F)) (s : MRing ι F) :
    segreLiftMap ι F W (segreIncl ι F s) = Polynomial.C (Ideal.Quotient.mk W s) := by
  have h : (segreLiftMap ι F W).comp (segreIncl ι F) =
      (IsScalarTower.toAlgHom F (MRing ι F ⧸ W) (Polynomial (MRing ι F ⧸ W))).comp
        (Ideal.Quotient.mkₐ F W) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [segreIncl, segreLiftMap, segreLiftVal]
  simpa using DFunLike.congr_fun h s

abbrev segreLiftAlgebra (W : Ideal (MRing ι F)) :
    Algebra (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) :=
  RingHom.toAlgebra' (Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom
    fun c x => mul_comm ((Ideal.kerLiftAlg (segreLiftMap ι F W)).toRingHom c) x

/- English proof (translation)
Set `_` to `segreLiftAlgebra W`. Establish `: (RingHom.ker (segreLiftMap ι F W)).IsPrime` using `RingHom.ker_isPrime _`. Establish `hmap : ∀ x, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ x) = segreLiftMap ι F W x` using `fun x => Ideal.kerLiftAlg_mk (segreLiftMap ι F W) x`. Use `choose c hc using hrel`. Establish `hm : Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩ : MRing ι F) ≠ 0`.

Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.prod_mem_iff]`. Simplify using `using hc`. Establish `hC : ∀ s : MRing ι F, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreIncl ι F s)) = Polynomial.C (Ideal.Quotient.mk W s)` using `fun s => by`. Rewrite using `[hmap, segreLiftMap_segreIncl]`. Establish `hY : algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreY c)) = Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))`.

Rewrite using `[hmap]`. Simplify using `[segreLiftMap, segreY, segreLiftVal]`. Establish `hX : IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial.X : Polynomial (MRing ι F ⧸ W))`. Use `⟨Polynomial.C (Ideal.Quotient.mk _ (segreIncl ι F (∏ k, X ⟨k, c k⟩))) * Polynomial.X - Polynomial.C (Ideal.Quotient.mk _ (segreY c)), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h1` using `congrArg (fun p => algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W)) (Polynomial.coeff p 1)) h`. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_true, one_ne_zero, if_false, sub_zero, Polynomial.coeff_zero, map_zero, hC, Polynomial.C_eq_zero] at h1`. Conclude with `hm h1`. Simplify using `only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hC, hY]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun p => ?_⟩` and prove the remaining obligations. Establish `: p ∈ Subalgebra.algebraicClosure (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W))`. Rewrite using `[p.as_sum_range_C_mul_X_pow]`. Use `Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)` and prove the remaining obligations. Take `⟨s, hs⟩` from `Ideal.Quotient.mk_surjective (p.coeff i)`.

Rewrite using `[← hs, ← hC]`. Conclude with `isAlgebraic_algebraMap _`. Conclude with `this`.
-/
theorem isAlgebraic_segreLift (W : Ideal (MRing ι F)) [W.IsPrime] (hrel : IsRelevant W) :
    letI := segreLiftAlgebra W
    Algebra.IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
  classical
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have hmap : ∀ x, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ x) = segreLiftMap ι F W x :=
    fun x => Ideal.kerLiftAlg_mk (segreLiftMap ι F W) x
  choose c hc using hrel
  have hm : Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩ : MRing ι F) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.IsPrime.prod_mem_iff]
    simpa using hc
  have hC : ∀ s : MRing ι F, algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreIncl ι F s)) =
        Polynomial.C (Ideal.Quotient.mk W s) := fun s => by
    rw [hmap, segreLiftMap_segreIncl]
  have hY : algebraMap (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) (Ideal.Quotient.mk _ (segreY c)) =
        Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩)) := by
    rw [hmap]
    simp [segreLiftMap, segreY, segreLiftVal]
  have hX : IsAlgebraic (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial.X : Polynomial (MRing ι F ⧸ W)) := by
    refine ⟨Polynomial.C (Ideal.Quotient.mk _ (segreIncl ι F (∏ k, X ⟨k, c k⟩))) * Polynomial.X -
      Polynomial.C (Ideal.Quotient.mk _ (segreY c)), ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun p => algebraMap
        (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
        (Polynomial (MRing ι F ⧸ W)) (Polynomial.coeff p 1)) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
        if_true, one_ne_zero, if_false, sub_zero, Polynomial.coeff_zero, map_zero, hC,
        Polynomial.C_eq_zero] at h1
      exact hm h1
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, hC, hY]
      ring
  refine ⟨fun p => ?_⟩
  have : p ∈ Subalgebra.algebraicClosure (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) := by
    rw [p.as_sum_range_C_mul_X_pow]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (p.coeff i)
    rw [← hs, ← hC]
    exact isAlgebraic_algebraMap _
  exact this

open Algebra in

/- English proof (translation)
Set `_ : ∀ x, Fintype (segreIdx ι x)` to `fun x => match x with`. Consider the case `.inl _ => (inferInstance : Fintype (∀ k, ι k))`. Consider the case `.inr k => (inferInstance : Fintype (ι k))`. Set `_` to `segreLiftAlgebra W`. Establish `: (RingHom.ker (segreLiftMap ι F W)).IsPrime` using `RingHom.ker_isPrime _`.

Establish `: IsScalarTower F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W))` using `IsScalarTower.of_algebraMap_eq fun c => ((Ideal.kerLiftAlg (segreLiftMap ι F W)).commutes c).symm`. Establish `: FaithfulSMul (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (Polynomial (MRing ι F ⧸ W))` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)`. Use `isAlgebraic_segreLift W hrel` as an intermediate fact. Take `⟨n, hA, htA⟩` from `GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)`. Establish `hP : trdeg F (Polynomial (MRing ι F ⧸ W)) = n + 1`.

Rewrite using `[← trdeg_add_eq F (MRing ι F ⧸ W) (A := Polynomial (MRing ι F ⧸ W)), Polynomial.trdeg_of_isDomain, htA]`. Establish `hQ : trdeg F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) = n + 1`. Establish `h2` using `trdeg_add_eq F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (A := Polynomial (MRing ι F ⧸ W))`. Rewrite `h2` using `[trdeg_eq_zero (R := MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) (A := Polynomial (MRing ι F ⧸ W)), add_zero]`. Rewrite using `[h2, hP]`.

Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hQ, hA]`. Simplify using the standard rewrite rules.
-/
theorem ringKrullDim_segreLift [∀ k, Fintype (ι k)] [DecidableEq K] (W : Ideal (MRing ι F))
    [W.IsPrime] (hrel : IsRelevant W) :
    ringKrullDim (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) =
      ringKrullDim (MRing ι F ⧸ W) + 1 := by
  let _ : ∀ x, Fintype (segreIdx ι x) := fun x => match x with
    | .inl _ => (inferInstance : Fintype (∀ k, ι k))
    | .inr k => (inferInstance : Fintype (ι k))
  let _ := segreLiftAlgebra W
  have : (RingHom.ker (segreLiftMap ι F W)).IsPrime := RingHom.ker_isPrime _
  have : IsScalarTower F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((Ideal.kerLiftAlg (segreLiftMap ι F W)).commutes c).symm
  have : FaithfulSMul (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (Polynomial (MRing ι F ⧸ W)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Ideal.kerLiftAlg_injective _)
  have := isAlgebraic_segreLift W hrel
  obtain ⟨n, hA, htA⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  have hP : trdeg F (Polynomial (MRing ι F ⧸ W)) = n + 1 := by
    rw [← trdeg_add_eq F (MRing ι F ⧸ W) (A := Polynomial (MRing ι F ⧸ W)),
      Polynomial.trdeg_of_isDomain, htA]
  have hQ : trdeg F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W)) = n + 1 := by
    have h2 := trdeg_add_eq F (MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W))
    rw [trdeg_eq_zero (R := MRing (segreIdx ι) F ⧸ RingHom.ker (segreLiftMap ι F W))
      (A := Polynomial (MRing ι F ⧸ W)), add_zero] at h2
    rw [h2, hP]
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, hQ, hA]
  simp

/- English proof (translation)
Introduce `F _ K _ _ ι _ W hW`. Use `hW.isPrime` as an intermediate fact. Establish `h` using `ringKrullDim_segreLift W hW.relevant`. Take `⟨n, hA, -⟩` from `GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)`. Unfold `relDim`.

Use `erw [h, hA]`. Rewrite using `[show ((n : WithBot ℕ∞) + 1) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast, show (n : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast]`. Simplify using `only [WithBot.map_coe, Fintype.card_sum, Fintype.card_unit]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `WithTop.map _ (WithTop.some (n + 1)) = WithTop.map _ (WithTop.some n)`.

Rewrite using `[WithTop.map_coe, WithTop.map_coe]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SegreLiftRelDim.proof : SegreLiftRelDim.Statement := by
  intro F _ K _ _ ι _ W hW
  have := hW.isPrime
  have h := ringKrullDim_segreLift W hW.relevant
  obtain ⟨n, hA, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ W)
  unfold relDim
  erw [h, hA]
  rw [show ((n : WithBot ℕ∞) + 1) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast,
    show (n : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) by norm_cast]
  simp only [WithBot.map_coe, Fintype.card_sum, Fintype.card_unit]
  congr 1
  change WithTop.map _ (WithTop.some (n + 1)) = WithTop.map _ (WithTop.some n)
  rw [WithTop.map_coe, WithTop.map_coe]
  congr 1
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
