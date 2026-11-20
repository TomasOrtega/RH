import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDenNotMem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Algebra ReciprocityTheory.ChartRestriction.G.Geo

namespace PtsChartDenNotMem

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[PtsSegreChart.segrePoly, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl fun k' hk' => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hk')]`.
-/
theorem segrePoly_update (a : (k : K) → ι k) (k : K) (j : ι k) :
    PtsSegreChart.segrePoly (Function.update a k j) =
      X (PtsSegreChart.coordEquiv ⟨k, j⟩) *
        ∏ k' ∈ Finset.univ.erase k, (X (PtsSegreChart.coordEquiv ⟨k', a k'⟩) :
          MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) := by
  rw [PtsSegreChart.segrePoly, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]

/- English proof (translation)
Repeatedly rewrite using `[segrePoly_update, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[PtsSegreChart.segrePoly, ← Finset.prod_pow]`. Rewrite using `[Finset.prod_comm' (t' := Finset.univ) (s' := fun k' => Finset.univ.erase k') (fun k k' => by simp [and_comm, eq_comm])]`. Use `Finset.prod_congr rfl fun k' _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`.
-/
theorem prod_segrePoly_update (a b : (k : K) → ι k) :
    ∏ k, PtsSegreChart.segrePoly (Function.update a k (b k)) =
      PtsSegreChart.segrePoly b * PtsSegreChart.segrePoly a ^ (Fintype.card K - 1) := by
  simp_rw [segrePoly_update, Finset.prod_mul_distrib]
  congr 1
  rw [PtsSegreChart.segrePoly, ← Finset.prod_pow]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun k' => Finset.univ.erase k')
    (fun k k' => by simp [and_comm, eq_comm])]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

def segreConeMap (J : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) :
    MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ]
      MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
  aeval fun a => X () * C (Ideal.Quotient.mk J (PtsSegreChart.segrePoly a))

open Classical in

def projForm {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (r : Fin (e + 1)) :
    MvPolynomial ((k : K) → ι k) ℂ :=
  ∑ a, C (Ψ (fun b => if a = b then 1 else 0) r) * X a

/- English proof (translation)
Rewrite using `[LinearMap.pi_apply_eq_sum_univ Ψ w]`. Simplify using `only [projForm, map_sum, map_mul, eval_C, eval_X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.
-/
theorem eval_projForm {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (r : Fin (e + 1))
    (w : ((k : K) → ι k) → ℂ) : eval w (projForm Ψ r) = Ψ w r := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ Ψ w]
  simp only [projForm, map_sum, map_mul, eval_C, eval_X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

/- English proof (translation)
Simplify using `only [projForm, PtsSegreChart.projPoly, segreConeMap, map_sum, map_mul, aeval_C, aeval_X, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hc : ∀ c : ℂ, Ideal.Quotient.mk J (C c : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = algebraMap ℂ _ c` using `fun c => rfl`. Rewrite using `[MvPolynomial.algebraMap_apply, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem segreConeMap_projForm (J : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (r : Fin (e + 1)) :
    segreConeMap J (projForm Ψ r) = X () * C (Ideal.Quotient.mk J (PtsSegreChart.projPoly Ψ r)) := by
  classical
  simp only [projForm, PtsSegreChart.projPoly, segreConeMap, map_sum, map_mul, aeval_C, aeval_X,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc : ∀ c : ℂ, Ideal.Quotient.mk J (C c : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) =
      algebraMap ℂ _ c := fun c => rfl
  rw [MvPolynomial.algebraMap_apply, hc]
  ring

omit [DecidableEq K] in

/- English proof (translation)
Establish `: (aeval fun q => (C (Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv q))) : MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))) = (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.c …`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `q`. Simplify using `[MvPolynomial.algebraMap_eq]`. Rewrite using `[this]`.

Simplify using `[MvPolynomial.algebraMap_eq]`.
-/
theorem aeval_C_mk_rename (J : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ))
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => (C (Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv q))) :
      MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))) f =
      C (Ideal.Quotient.mk J (rename PtsSegreChart.coordEquiv f)) := by
  have : (aeval fun q => (C (Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv q))) :
      MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))) =
      (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)
        (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))).comp
        ((Ideal.Quotient.mkₐ ℂ J).comp (rename PtsSegreChart.coordEquiv)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [MvPolynomial.algebraMap_eq]
  rw [this]
  simp [MvPolynomial.algebraMap_eq]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `: IsDomain (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` using `Ideal.Quotient.isDomain J`. Set `θ : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` to `segreConeMap J`. Use `show ringKrullDim (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) = _`. Establish `: (RingHom.ker θ).IsPrime` using `RingHom.ker_isPrime _`. Establish `: IsDomain (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)` using `Ideal.Quotient.isDomain _`.

Set `κ : (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) →ₐ[ℂ] MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` to `Ideal.kerLiftAlg θ`. Establish `hκ : Function.Injective κ` using `Ideal.kerLiftAlg_injective θ`. Set `_ : Algebra (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` to `κ.toRingHom.toAlgebra`. Establish `: IsScalarTower ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` using `IsScalarTower.of_algebraMap_eq fun c => (κ.commutes c).symm`. Establish `hκmk : ∀ f, algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) (Ideal.Quotient.mk _ f) = θ f` using `fun f => Ideal.kerLiftAlg_mk θ f`.

Establish `: Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)`. Establish `: Algebra.FiniteType ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)`. Take `⟨sA, hAdim, hAtr⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))`. Take `⟨sR, hRdim, hRtr⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ))`. Establish `: FaithfulSMul ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)` using `(faithfulSMul_iff_algebraMap_injective ℂ _).mpr (algebraMap ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)).injective`.

Establish `: FaithfulSMul (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective Unit _)`. Establish `: FaithfulSMul ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)` using `(faithfulSMul_iff_algebraMap_injective ℂ _).mpr (algebraMap ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)).injective`. Establish `: FaithfulSMul (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hκ`. Establish `hT1 : trdeg ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) + trdeg (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = trdeg ℂ (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ …` using `trdeg_add_eq ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)`. Establish `hmk1 : ∀ k, Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv ⟨k, i k⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = 1`.

Introduce `k`. Rewrite using `[← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]`. Conclude with `h1 k`. Establish `hmkE : ∀ k, Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase k, (X (PtsSegreChart.coordEquiv ⟨k', i k'⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) = 1`. Introduce `k`.

Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_one fun k' _ => hmk1 k'`. Establish `hmkI : Ideal.Quotient.mk J (PtsSegreChart.segrePoly i) = 1`. Rewrite using `[PtsSegreChart.segrePoly, map_prod]`. Conclude with `Finset.prod_eq_one fun k _ => hmk1 k`.

Establish `hT : θ (X i) = X ()`. Simplify using `only [θ, segreConeMap, aeval_X, hmkI, map_one, mul_one]`. Establish `hTx : ∀ c : Fin (Fintype.card (Σ k, ι k)), θ (X (Function.update i (PtsSegreChart.coordEquiv.symm c).1 (PtsSegreChart.coordEquiv.symm c).2)) = X () * C (Ideal.Quotient.mk J (X c))`. Introduce `c`. Simplify using `only [θ, segreConeMap, aeval_X, segrePoly_update, map_mul, hmkE, mul_one, Sigma.eta, Equiv.apply_symm_apply]`.

Set `AC` to `Subalgebra.algebraicClosure (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))`. Establish `hRAC : ∀ f, θ f ∈ AC` using `fun f => by`. Rewrite using `[Subalgebra.mem_algebraicClosure, ← hκmk]`. Conclude with `isAlgebraic_algebraMap _`. Establish `hyAC : ∀ c : Fin (Fintype.card (Σ k, ι k)), C (Ideal.Quotient.mk J (X c)) ∈ AC` using `fun c => by`.

Establish `h2` using `hRAC (X i)`. Establish `h3` using `hRAC (X (Function.update i (PtsSegreChart.coordEquiv.symm c).1 (PtsSegreChart.coordEquiv.symm c).2))`. Rewrite `h2` using `[hT]`. Rewrite `h3` using `[hTx]`. Conclude with `(Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (X_ne_zero ())) ((Subalgebra.mem_algebraicClosure _ _).mp h2) ((Subalgebra.mem_algebraicClosure _ _).mp h3))`.

Establish `hCAC : ∀ f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ, C (Ideal.Quotient.mk J f) ∈ AC`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c`. Establish `h2` using `hRAC (C c)`.

Establish `h3 : θ (C c) = C (Ideal.Quotient.mk J (C c))`. Simplify using `only [θ, segreConeMap, aeval_C, MvPolynomial.algebraMap_apply]`. Both sides reduce to the same expression. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Consider the case `add f g hf hg`.

Rewrite using `[map_add, map_add]`. Conclude with `AC.add_mem hf hg`. Consider the case `mul_X f c hf`. Rewrite using `[map_mul, map_mul]`. Conclude with `AC.mul_mem hf (hyAC c)`.

Establish `hall : ∀ t : MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J), t ∈ AC`. Introduce `t`. Proceed by induction on `t using MvPolynomial.induction_on with`. Consider the case `C a`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Conclude with `hCAC f`. Consider the case `add f g hf hg => exact AC.add_mem hf hg`. Consider the case `mul_X f u hf`. Establish `h2` using `hRAC (X i)`. Rewrite `h2` using `[hT]`.

Conclude with `AC.mul_mem hf h2`. Establish `: Algebra.IsAlgebraic (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` using `⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩`. Establish `hT2 : trdeg ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) + trdeg (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = trdeg ℂ (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))` using `trdeg_add_eq ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)`. Establish `h0 : trdeg (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = 0` using `trdeg_eq_zero`. Rewrite `hT2` using `[h0, add_zero]`.

Establish `hK : trdeg (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = (1 : Cardinal)`. Rewrite using `[MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]`. Rewrite `hT1` using `[hK, hAtr, ← hT2, hRtr]`. Establish `hnat : sA + 1 = sR` using `by exact_mod_cast hT1`. Establish `hsA : sA = d`.

Rewrite `hd` using `[hAdim]`. Conclude with `hd` after adjusting the coercions. Rewrite using `[hRdim, ← hnat, hsA]`.
-/
theorem ringKrullDim_ker_segreConeMap (J : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) [J.IsPrime]
    (i : (k : K) → ι k)
    (h1 : ∀ k, (X (PtsSegreChart.coordEquiv ⟨k, i k⟩) - 1 : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) ∈ J)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) = (d : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker (segreConeMap J)) =
      ((d + 1 : ℕ) : WithBot ℕ∞) := by
  classical
  have : IsDomain (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) := Ideal.Quotient.isDomain J
  let θ : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ]
      MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) := segreConeMap J
  show ringKrullDim (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) = _
  have : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime _
  have : IsDomain (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) := Ideal.Quotient.isDomain _
  let κ : (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) →ₐ[ℂ]
      MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    Ideal.kerLiftAlg θ
  have hκ : Function.Injective κ := Ideal.kerLiftAlg_injective θ
  let _ : Algebra (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    κ.toRingHom.toAlgebra
  have : IsScalarTower ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    IsScalarTower.of_algebraMap_eq fun c => (κ.commutes c).symm
  have hκmk : ∀ f, algebraMap (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))
      (Ideal.Quotient.mk _ f) = θ f := fun f => Ideal.kerLiftAlg_mk θ f
  have : Algebra.FiniteType ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  obtain ⟨sA, hAdim, hAtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))
  obtain ⟨sR, hRdim, hRtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ))
  have : FaithfulSMul ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr
      (algebraMap ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)).injective
  have : FaithfulSMul (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective Unit _)
  have : FaithfulSMul ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) :=
    (faithfulSMul_iff_algebraMap_injective ℂ _).mpr
      (algebraMap ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)).injective
  have : FaithfulSMul (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hκ
  have hT1 : trdeg ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) +
      trdeg (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)
        (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) =
      trdeg ℂ (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    trdeg_add_eq ℂ (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)
  have hmk1 : ∀ k, Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv ⟨k, i k⟩) :
      MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact h1 k
  have hmkE : ∀ k, Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase k,
      (X (PtsSegreChart.coordEquiv ⟨k', i k'⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) = 1 := by
    intro k
    rw [map_prod]
    exact Finset.prod_eq_one fun k' _ => hmk1 k'
  have hmkI : Ideal.Quotient.mk J (PtsSegreChart.segrePoly i) = 1 := by
    rw [PtsSegreChart.segrePoly, map_prod]
    exact Finset.prod_eq_one fun k _ => hmk1 k
  have hT : θ (X i) = X () := by
    simp only [θ, segreConeMap, aeval_X, hmkI, map_one, mul_one]
  have hTx : ∀ c : Fin (Fintype.card (Σ k, ι k)),
      θ (X (Function.update i (PtsSegreChart.coordEquiv.symm c).1 (PtsSegreChart.coordEquiv.symm c).2)) =
        X () * C (Ideal.Quotient.mk J (X c)) := by
    intro c
    simp only [θ, segreConeMap, aeval_X, segrePoly_update, map_mul, hmkE, mul_one, Sigma.eta,
      Equiv.apply_symm_apply]
  let AC := Subalgebra.algebraicClosure (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
    (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))
  have hRAC : ∀ f, θ f ∈ AC := fun f => by
    rw [Subalgebra.mem_algebraicClosure, ← hκmk]
    exact isAlgebraic_algebraMap _
  have hyAC : ∀ c : Fin (Fintype.card (Σ k, ι k)), C (Ideal.Quotient.mk J (X c)) ∈ AC := fun c => by
    have h2 := hRAC (X i)
    have h3 := hRAC (X (Function.update i (PtsSegreChart.coordEquiv.symm c).1 (PtsSegreChart.coordEquiv.symm c).2))
    rw [hT] at h2
    rw [hTx] at h3
    exact (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero ()))
      ((Subalgebra.mem_algebraicClosure _ _).mp h2) ((Subalgebra.mem_algebraicClosure _ _).mp h3))
  have hCAC : ∀ f : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ, C (Ideal.Quotient.mk J f) ∈ AC := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      have h2 := hRAC (C c)
      have h3 : θ (C c) = C (Ideal.Quotient.mk J (C c)) := by
        simp only [θ, segreConeMap, aeval_C, MvPolynomial.algebraMap_apply]
        rfl
      rwa [h3] at h2
    | add f g hf hg =>
      rw [map_add, map_add]
      exact AC.add_mem hf hg
    | mul_X f c hf =>
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC c)
  have hall : ∀ t : MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J), t ∈ AC := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    | add f g hf hg => exact AC.add_mem hf hg
    | mul_X f u hf =>
      have h2 := hRAC (X i)
      rw [hT] at h2
      exact AC.mul_mem hf h2
  have : Algebra.IsAlgebraic (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ) +
      trdeg (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
        (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) =
      trdeg ℂ (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) :=
    trdeg_add_eq ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
  have h0 : trdeg (MvPolynomial ((k : K) → ι k) ℂ ⧸ RingHom.ker θ)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = 0 :=
    trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)
      (MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) = (1 : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + 1 = sR := by exact_mod_cast hT1
  have hsA : sA = d := by
    rw [hAdim] at hd
    exact_mod_cast hd
  rw [hRdim, ← hnat, hsA]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `ℓ V s hV _ _ hs hds`. Conclude with `⟨V, hV, le_rfl, fun j => j.elim0, s, hs, by omega⟩`.

Consider the case `succ n ih`. Introduce `ℓ V s hV hVM hℓ hs hds`. Distinguish the cases in `h0 : ℓ 0 ∈ V`. Take `⟨W, hW, hVW, hℓW, t, ht, hdt⟩` from `ih (fun j => ℓ j.succ) V s hV hVM (fun j => hℓ _) hs (by omega)`. Use `⟨W, hW, hVW, fun j => ?_, t, ht, hdt⟩` and prove the remaining obligations.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact hVW h0`. Consider the case `succ j => exact hℓW j`. Take `⟨W1, hW1, hW1M⟩` from `Ideal.exists_minimalPrimes_le (sup_le hVM ((Ideal.span_singleton_le_iff_mem _).2 (hℓ 0)))`. Establish `: W1.IsPrime` using `hW1.1.1`.

Establish `hpit` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ σ V W1 (ℓ 0) hV h0 hW1`. Establish `: IsDomain (MvPolynomial σ ℂ ⧸ W1)` using `Ideal.Quotient.isDomain W1`. Establish `: Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ W1)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ W1) (Ideal.Quotient.mkₐ_surjective ℂ W1)`. Take `⟨s1, hs1, -⟩` from `ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial σ ℂ ⧸ W1)`. Rewrite `hpit` using `[hs1, hs]`.

Establish `hs1s : s1 + 1 = s` using `by exact_mod_cast hpit`. Take `⟨W, hW, hW1W, hℓW, t, ht, hdt⟩` from `ih (fun j => ℓ j.succ) W1 s1 hW1.1.1 hW1M (fun j => hℓ _) hs1 (by omega)`. Establish `hVW1 : V ≤ W1` using `le_sup_left.trans hW1.1.2`. Establish `h0W1 : ℓ 0 ∈ W1` using `hW1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Use `⟨W, hW, hVW1.trans hW1W, fun j => ?_, t, ht, hdt⟩` and prove the remaining obligations.

Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact hW1W h0W1`. Consider the case `succ j => exact hℓW j`.
-/
theorem exists_prime_cut {σ : Type} [Fintype σ] (M : Ideal (MvPolynomial σ ℂ)) [M.IsPrime] (d : ℕ) :
    ∀ (n : ℕ) (ℓ : Fin n → MvPolynomial σ ℂ) (V : Ideal (MvPolynomial σ ℂ)) (s : ℕ), V.IsPrime → V ≤ M →
      (∀ j, ℓ j ∈ M) → ringKrullDim (MvPolynomial σ ℂ ⧸ V) = (s : WithBot ℕ∞) → d + n ≤ s →
      ∃ W : Ideal (MvPolynomial σ ℂ), W.IsPrime ∧ V ≤ W ∧ (∀ j, ℓ j ∈ W) ∧
        ∃ t : ℕ, ringKrullDim (MvPolynomial σ ℂ ⧸ W) = (t : WithBot ℕ∞) ∧ d ≤ t := by
  intro n
  induction n with
  | zero =>
    intro ℓ V s hV _ _ hs hds
    exact ⟨V, hV, le_rfl, fun j => j.elim0, s, hs, by omega⟩
  | succ n ih =>
    intro ℓ V s hV hVM hℓ hs hds
    by_cases h0 : ℓ 0 ∈ V
    · obtain ⟨W, hW, hVW, hℓW, t, ht, hdt⟩ :=
        ih (fun j => ℓ j.succ) V s hV hVM (fun j => hℓ _) hs (by omega)
      refine ⟨W, hW, hVW, fun j => ?_, t, ht, hdt⟩
      induction j using Fin.cases with
      | zero => exact hVW h0
      | succ j => exact hℓW j
    · obtain ⟨W1, hW1, hW1M⟩ := Ideal.exists_minimalPrimes_le
        (sup_le hVM ((Ideal.span_singleton_le_iff_mem _).2 (hℓ 0)))
      have : W1.IsPrime := hW1.1.1
      have hpit := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ σ V W1 (ℓ 0) hV h0 hW1
      have : IsDomain (MvPolynomial σ ℂ ⧸ W1) := Ideal.Quotient.isDomain W1
      have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ W1) :=
        Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ W1) (Ideal.Quotient.mkₐ_surjective ℂ W1)
      obtain ⟨s1, hs1, -⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := MvPolynomial σ ℂ ⧸ W1)
      rw [hs1, hs] at hpit
      have hs1s : s1 + 1 = s := by exact_mod_cast hpit
      obtain ⟨W, hW, hW1W, hℓW, t, ht, hdt⟩ :=
        ih (fun j => ℓ j.succ) W1 s1 hW1.1.1 hW1M (fun j => hℓ _) hs1 (by omega)
      have hVW1 : V ≤ W1 := le_sup_left.trans hW1.1.2
      have h0W1 : ℓ 0 ∈ W1 := hW1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      refine ⟨W, hW, hVW1.trans hW1W, fun j => ?_, t, ht, hdt⟩
      induction j using Fin.cases with
      | zero => exact hW1W h0W1
      | succ j => exact hℓW j

/- English proof (translation)
Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_and, not_not] at h`. Establish `hv : vanishingIdeal ℂ (zeroLocus ℂ W) = W.radical` using `vanishingIdeal_zeroLocus_eq_radical (K := ℂ) W`. Establish `hX : ∀ a, (X a : MvPolynomial σ ℂ) ∈ W`. Introduce `a`.

Rewrite using `[← Ideal.IsPrime.radical (inferInstance : W.IsPrime), ← hv, mem_vanishingIdeal_iff]`. Introduce `x hx`. Rewrite using `[h x hx, aeval_X, Pi.zero_apply]`. Establish `hsurj : Function.Surjective (algebraMap ℂ (MvPolynomial σ ℂ ⧸ W))`. Introduce `x`.

Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => exact ⟨c, rfl⟩`. Consider the case `add f g hf hg`. Take `⟨c1, hc1⟩` from `hf`.

Take `⟨c2, hc2⟩` from `hg`. Conclude with `⟨c1 + c2, by rw [map_add, hc1, hc2, map_add]⟩`. Consider the case `mul_X f a _`. Conclude with `⟨0, by rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (hX a), mul_zero, map_zero]⟩`. Establish `hle` using `ringKrullDim_le_of_surjective _ hsurj`.

Rewrite `hle` using `[ringKrullDim_eq_zero_of_field]`. Use `hW.trans hle` as an intermediate fact. Conclude with `absurd this (by decide)`.
-/
theorem exists_ne_zero_mem_zeroLocus {σ : Type} [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) [W.IsPrime]
    (hW : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ W)) :
    ∃ w ∈ zeroLocus ℂ W, w ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hv : vanishingIdeal ℂ (zeroLocus ℂ W) = W.radical := vanishingIdeal_zeroLocus_eq_radical (K := ℂ) W
  have hX : ∀ a, (X a : MvPolynomial σ ℂ) ∈ W := by
    intro a
    rw [← Ideal.IsPrime.radical (inferInstance : W.IsPrime), ← hv, mem_vanishingIdeal_iff]
    intro x hx
    rw [h x hx, aeval_X, Pi.zero_apply]
  have hsurj : Function.Surjective (algebraMap ℂ (MvPolynomial σ ℂ ⧸ W)) := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction f using MvPolynomial.induction_on with
    | C c => exact ⟨c, rfl⟩
    | add f g hf hg =>
      obtain ⟨c1, hc1⟩ := hf
      obtain ⟨c2, hc2⟩ := hg
      exact ⟨c1 + c2, by rw [map_add, hc1, hc2, map_add]⟩
    | mul_X f a _ =>
      exact ⟨0, by rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (hX a), mul_zero, map_zero]⟩
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [ringKrullDim_eq_zero_of_field] at hle
  have := hW.trans hle
  exact absurd this (by decide)

/- English proof (translation)
Use `⟨fun k => ⟨a k, by simpa using ha⟩, ?_⟩` and prove the remaining obligations. Set `Φ : MRing ι →+* MvPolynomial ((k : K) → ι k) ℂ` to `(rename fun q : Σ k, ι k => Function.update a q.1 q.2).toRingHom.comp (map (Int.castRingHom ℂ))`. Establish `hle : P ≤ (RingHom.ker (segreConeMap J)).comap Φ`. Take `⟨S, hS, hPS⟩` from `hP`. Rewrite using `[hPS, Ideal.span_le]`.

Introduce `g hg`. Take `⟨b, hb⟩` from `hS g hg`. Establish `hgh : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) g) b` using `fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k`. Establish `hgJ : rename PtsSegreChart.coordEquiv (map (Int.castRingHom ℂ) g) ∈ J` using `hJP g (by rw [hPS]; exact Ideal.subset_span hg)`. Use `show segreConeMap J (rename _ (map (Int.castRingHom ℂ) g)) = 0`.

Rewrite using `[segreConeMap, aeval_rename]`. Establish `hpt : ((fun a => (X () * C (Ideal.Quotient.mk J (PtsSegreChart.segrePoly a)) : MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))) ∘ fun q : Σ k, ι k => Function.update a q.1 q.2) = fun q => (X () * C (Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase q.1, (X (Pt …`. Use function extensionality and compare the values at `q`. Simplify using `only [Function.comp_apply, segrePoly_update, map_mul, Sigma.eta]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs` using `ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hgh (fun k => (X () * C (Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase k, (X (PtsSegreChart.coordEquiv ⟨k', a k'⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ))) : MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, …`. Use `beta_reduce at hs`. Rewrite using `[hpt, hs, aeval_C_mk_rename, Ideal.Quotient.eq_zero_iff_mem.2 hgJ, map_zero, mul_zero]`. Introduce `f hf`. Use `hw _ (hle hf)` as an intermediate fact.

Simplify `this` using `[Φ, eval_rename, Function.comp_def]`.
-/
theorem mem_mcPts_update (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P)
    (J : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ))
    (hJP : ∀ f ∈ P, rename PtsSegreChart.coordEquiv (map (Int.castRingHom ℂ) f) ∈ J)
    (w : ((k : K) → ι k) → ℂ) (hw : ∀ f ∈ RingHom.ker (segreConeMap J), eval w f = 0)
    (a : (k : K) → ι k) (ha : w a ≠ 0) :
    (fun q : Σ k, ι k => w (Function.update a q.1 q.2)) ∈ mcPts P := by
  refine ⟨fun k => ⟨a k, by simpa using ha⟩, ?_⟩
  let Φ : MRing ι →+* MvPolynomial ((k : K) → ι k) ℂ :=
    (rename fun q : Σ k, ι k => Function.update a q.1 q.2).toRingHom.comp (map (Int.castRingHom ℂ))
  have hle : P ≤ (RingHom.ker (segreConeMap J)).comap Φ := by
    obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro g hg
    obtain ⟨b, hb⟩ := hS g hg
    have hgh : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) g) b :=
      fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k
    have hgJ : rename PtsSegreChart.coordEquiv (map (Int.castRingHom ℂ) g) ∈ J :=
      hJP g (by rw [hPS]; exact Ideal.subset_span hg)
    show segreConeMap J (rename _ (map (Int.castRingHom ℂ) g)) = 0
    rw [segreConeMap, aeval_rename]
    have hpt : ((fun a => (X () * C (Ideal.Quotient.mk J (PtsSegreChart.segrePoly a)) :
        MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))) ∘
        fun q : Σ k, ι k => Function.update a q.1 q.2) =
        fun q => (X () * C (Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase q.1,
          (X (PtsSegreChart.coordEquiv ⟨k', a k'⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)))) *
          C (Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv q))) := by
      funext q
      simp only [Function.comp_apply, segrePoly_update, map_mul, Sigma.eta]
      ring
    have hs := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog hgh
      (fun k => (X () * C (Ideal.Quotient.mk J (∏ k' ∈ Finset.univ.erase k,
        (X (PtsSegreChart.coordEquiv ⟨k', a k'⟩) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ))) :
          MvPolynomial Unit (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)))
      (fun q => C (Ideal.Quotient.mk J (X (PtsSegreChart.coordEquiv q))))
    beta_reduce at hs
    rw [hpt, hs, aeval_C_mk_rename,
      Ideal.Quotient.eq_zero_iff_mem.2 hgJ, map_zero, mul_zero]
  intro f hf
  have := hw _ (hle hf)
  simpa [Φ, eval_rename, Function.comp_def] using this

end PtsChartDenNotMem

open PtsChartDenNotMem in

/- English proof (translation)
Introduce `K _ _ ι _ P e i Ψ hP hΨ J hJ hmem`. Establish `: J.IsPrime` using `hJ.1.1`. Establish `hIJ` using `hJ.1.2`. Establish `h1 : ∀ k, (X (PtsSegreChart.coordEquiv ⟨k, i k⟩) - 1 : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) ∈ J` using `fun k => hIJ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))`. Establish `hJP : ∀ f ∈ P, rename PtsSegreChart.coordEquiv (map (Int.castRingHom ℂ) f) ∈ J` using `fun f hf => hIJ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))`.

Establish `hdD` using `h K ι P e i hP J hJ`. Establish `: (RingHom.ker (segreConeMap (K` using `K) (ι := ι) J)).IsPrime := RingHom.ker_isPrime _`. Establish `hdim` using `ringKrullDim_ker_segreConeMap J i h1 e hdD`. Establish `hmem' : PtsSegreChart.projPoly Ψ 0 ∈ J` using `hmem`. Establish `hℓ0 : projForm Ψ 0 ∈ RingHom.ker (segreConeMap (K` using `K) (ι := ι) J) := by`.

Rewrite using `[RingHom.mem_ker, segreConeMap_projForm, Ideal.Quotient.eq_zero_iff_mem.2 hmem', map_zero, mul_zero]`. Set `M : Ideal (MvPolynomial ((k : K) → ι k) ℂ)` to `RingHom.ker (eval (0 : ((k : K) → ι k) → ℂ))`. Establish `: M.IsPrime` using `RingHom.ker_isPrime _`. Establish `hSM : RingHom.ker (segreConeMap (K` using `K) (ι := ι) J) ≤ M := by`. Introduce `f hf`.

Establish `hε : ∀ g, aeval (fun _ : Unit => (0 : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J)) (segreConeMap J g) = algebraMap ℂ _ (eval 0 g)`. Introduce `g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C c => simp [segreConeMap]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.

Consider the case `mul_X f a _ => simp [map_mul, segreConeMap]`. Use `hε f` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker.1 hf, map_zero]`. Conclude with `(map_eq_zero_iff _ (algebraMap ℂ _).injective).1 this.symm`. Establish `hℓM : ∀ r, projForm Ψ r ∈ M` using `fun r => RingHom.mem_ker.2 (by rw [eval_projForm, map_zero, Pi.zero_apply])`.

Take `⟨W, hW, hSW, hℓW, t, ht, h1t⟩` from `exists_prime_cut M 1 e (fun j => projForm Ψ j.succ) (RingHom.ker (segreConeMap (K := K) (ι := ι) J)) (e + 1) inferInstance hSM (fun j => hℓM _) hdim (by omega)`. Establish `: W.IsPrime` using `hW`. Take `⟨w, hwW, hw0⟩` from `exists_ne_zero_mem_zeroLocus W (by rw [ht]; exact_mod_cast h1t)`. Establish `hwW' : ∀ f ∈ W, eval w f = 0` using `fun f hf => by`. Simplify using `using (mem_zeroLocus_iff.1 hwW) f hf`.

Establish `hwS : ∀ f ∈ RingHom.ker (segreConeMap (K` using `K) (ι := ι) J), eval w f = 0 := fun f hf => hwW' f (hSW hf)`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hw0`. Establish `hy` using `mem_mcPts_update P hP.2.1.2.1 J hJP w hwS a ha`. Apply `hΨ _ hy` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1 := by`.

Establish `: Nonempty K` using `hP.1`. Conclude with `⟨Fintype.card K - 1, by have := Fintype.card_pos (α := K); omega⟩`. Establish `hseg : segre (fun q : Σ k, ι k => w (Function.update a q.1 q.2)) = (w a) ^ c • w`. Use function extensionality and compare the values at `b`. Establish `hrel : X b * X a ^ c - ∏ k, X (Function.update a k (b k)) ∈ RingHom.ker (segreConeMap (K` using `K) (ι := ι) J) := by`.

Establish `hprod` using `prod_segrePoly_update a b`. Rewrite `hprod` using `[hc, Nat.add_sub_cancel]`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_pow, map_prod]`. Simplify using `only [segreConeMap, aeval_X]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hc, ← map_prod C, ← map_prod (Ideal.Quotient.mk J), hprod]`.

Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `hwS _ hrel` as an intermediate fact. Simplify using `only [map_sub, map_mul, map_pow, map_prod, eval_X] at this`. Simplify using `only [segre, Pi.smul_apply, smul_eq_mul]`.

Rewrite `this` using `[sub_eq_zero]`. Rewrite using `[← this, mul_comm]`. Establish `hΨw : Ψ w = 0`. Use function extensionality and compare the values at `r`. Rewrite using `[Pi.zero_apply, ← eval_projForm]`.

Proceed by induction on `r using Fin.cases with`. Consider the case `zero => exact hwS _ hℓ0`. Consider the case `succ j => exact hwW' _ (hℓW j)`. Rewrite using `[hseg, map_smul, hΨw, smul_zero]`.
-/
theorem PtsChartDenNotMem.proof (h : PtsChartDim.Statement) : PtsChartDenNotMem.Statement := by
  classical
  intro K _ _ ι _ P e i Ψ hP hΨ J hJ hmem
  have : J.IsPrime := hJ.1.1
  have hIJ := hJ.1.2
  have h1 : ∀ k, (X (PtsSegreChart.coordEquiv ⟨k, i k⟩) - 1 :
      MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) ∈ J :=
    fun k => hIJ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hJP : ∀ f ∈ P, rename PtsSegreChart.coordEquiv (map (Int.castRingHom ℂ) f) ∈ J :=
    fun f hf => hIJ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have hdD := h K ι P e i hP J hJ
  have : (RingHom.ker (segreConeMap (K := K) (ι := ι) J)).IsPrime := RingHom.ker_isPrime _
  have hdim := ringKrullDim_ker_segreConeMap J i h1 e hdD
  have hmem' : PtsSegreChart.projPoly Ψ 0 ∈ J := hmem
  have hℓ0 : projForm Ψ 0 ∈ RingHom.ker (segreConeMap (K := K) (ι := ι) J) := by
    rw [RingHom.mem_ker, segreConeMap_projForm, Ideal.Quotient.eq_zero_iff_mem.2 hmem', map_zero, mul_zero]

  let M : Ideal (MvPolynomial ((k : K) → ι k) ℂ) := RingHom.ker (eval (0 : ((k : K) → ι k) → ℂ))
  have : M.IsPrime := RingHom.ker_isPrime _
  have hSM : RingHom.ker (segreConeMap (K := K) (ι := ι) J) ≤ M := by
    intro f hf
    have hε : ∀ g, aeval (fun _ : Unit => (0 : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J))
        (segreConeMap J g) = algebraMap ℂ _ (eval 0 g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C c => simp [segreConeMap]
      | add f g hf hg => simp only [map_add, hf, hg]
      | mul_X f a _ => simp [map_mul, segreConeMap]
    have := hε f
    rw [RingHom.mem_ker.1 hf, map_zero] at this
    exact (map_eq_zero_iff _ (algebraMap ℂ _).injective).1 this.symm
  have hℓM : ∀ r, projForm Ψ r ∈ M := fun r =>
    RingHom.mem_ker.2 (by rw [eval_projForm, map_zero, Pi.zero_apply])
  obtain ⟨W, hW, hSW, hℓW, t, ht, h1t⟩ := exists_prime_cut M 1 e (fun j => projForm Ψ j.succ)
    (RingHom.ker (segreConeMap (K := K) (ι := ι) J)) (e + 1) inferInstance hSM (fun j => hℓM _) hdim (by omega)
  have : W.IsPrime := hW
  obtain ⟨w, hwW, hw0⟩ := exists_ne_zero_mem_zeroLocus W (by rw [ht]; exact_mod_cast h1t)
  have hwW' : ∀ f ∈ W, eval w f = 0 := fun f hf => by
    simpa using (mem_zeroLocus_iff.1 hwW) f hf
  have hwS : ∀ f ∈ RingHom.ker (segreConeMap (K := K) (ι := ι) J), eval w f = 0 :=
    fun f hf => hwW' f (hSW hf)
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hw0
  have hy := mem_mcPts_update P hP.2.1.2.1 J hJP w hwS a ha
  apply hΨ _ hy
  obtain ⟨c, hc⟩ : ∃ c, Fintype.card K = c + 1 := by
    have : Nonempty K := hP.1
    exact ⟨Fintype.card K - 1, by have := Fintype.card_pos (α := K); omega⟩
  have hseg : segre (fun q : Σ k, ι k => w (Function.update a q.1 q.2)) = (w a) ^ c • w := by
    funext b
    have hrel : X b * X a ^ c - ∏ k, X (Function.update a k (b k)) ∈
        RingHom.ker (segreConeMap (K := K) (ι := ι) J) := by
      have hprod := prod_segrePoly_update a b
      rw [hc, Nat.add_sub_cancel] at hprod
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_prod]
      simp only [segreConeMap, aeval_X]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hc, ← map_prod C,
        ← map_prod (Ideal.Quotient.mk J), hprod]
      simp only [map_mul, map_pow]
      ring
    have := hwS _ hrel
    simp only [map_sub, map_mul, map_pow, map_prod, eval_X] at this
    simp only [segre, Pi.smul_apply, smul_eq_mul]
    rw [sub_eq_zero] at this
    rw [← this, mul_comm]
  have hΨw : Ψ w = 0 := by
    funext r
    rw [Pi.zero_apply, ← eval_projForm]
    induction r using Fin.cases with
    | zero => exact hwS _ hℓ0
    | succ j => exact hwW' _ (hℓW j)
  rw [hseg, map_smul, hΨw, smul_zero]

end GroundTheory.Heights₂.Heights
