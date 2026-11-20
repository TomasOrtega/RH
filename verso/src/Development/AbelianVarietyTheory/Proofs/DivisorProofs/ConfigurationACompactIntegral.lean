import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaPolynomialLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.FockBridge
open scoped Classical

namespace GlobalTheory.FockLowStab

open GlobalTheory.RealLift Formalism.BasicNotions.TH

/- English proof (translation)
Set `N` to `MvPolynomial.restrictTotalDegree (Ix p q × Ix r s) ℂ g.totalDegree`. Establish `hN : fockAct2 p q r s Y g ∈ N`. Establish `e : fockAct2 p q r s Y g = ∑ i ∈ Finset.range (g.totalDegree + 1), fockAct2 p q r s Y (MvPolynomial.homogeneousComponent i g)`. Rewrite using `[← map_sum, MvPolynomial.sum_homogeneousComponent]`. Rewrite using `[e]`.

Use `N.sum_mem fun i hi => ?_` and prove the remaining obligations. Establish `hm : fockAct2 p q r s Y (MvPolynomial.homogeneousComponent i g) ∈ homog (Ix p q × Ix r s) i`. Rewrite using `[GlobalTheory.FockDeg.fockAct2_eq]`. Conclude with `GlobalTheory.FockDeg.omAct_mem_homog (fun l l' h => GlobalTheory.FockDeg.lineMatrixKroneckerRightFactor_eq_zero_of_isKC hY l l' h) (MvPolynomial.homogeneousComponent_mem i g)`. Rewrite using `[MvPolynomial.mem_restrictTotalDegree]`.

Use `((MvPolynomial.mem_homogeneousSubmodule _ _).1 hm).totalDegree_le` as an intermediate fact. Establish `hi'` using `Finset.mem_range.1 hi`. Use linear arithmetic over natural numbers and integers. Conclude with `(MvPolynomial.mem_restrictTotalDegree _ _ _).1 hN`.
-/
theorem totalDegree_fockAct2_le {p q r s : ℕ} {Y : Mat r s} (hY : IsKC Y) (g : Formalism.BasicNotions.TH.Pol p q r s) :
    (fockAct2 p q r s Y g).totalDegree ≤ g.totalDegree := by
  let N := MvPolynomial.restrictTotalDegree (Ix p q × Ix r s) ℂ g.totalDegree
  have hN : fockAct2 p q r s Y g ∈ N := by
    have e : fockAct2 p q r s Y g = ∑ i ∈ Finset.range (g.totalDegree + 1),
        fockAct2 p q r s Y (MvPolynomial.homogeneousComponent i g) := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    rw [e]
    refine N.sum_mem fun i hi => ?_
    have hm : fockAct2 p q r s Y (MvPolynomial.homogeneousComponent i g) ∈ homog (Ix p q × Ix r s) i := by
      rw [GlobalTheory.FockDeg.fockAct2_eq]
      exact GlobalTheory.FockDeg.omAct_mem_homog (fun l l' h => GlobalTheory.FockDeg.lineMatrixKroneckerRightFactor_eq_zero_of_isKC hY l l' h)
        (MvPolynomial.homogeneousComponent_mem i g)
    rw [MvPolynomial.mem_restrictTotalDegree]
    have := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hm).totalDegree_le
    have hi' := Finset.mem_range.1 hi
    omega
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).1 hN

/- English proof (translation)
Establish `hle : GlobalTheory.KFixIrr.degLE ι P Q R S k ≤ (GlobalTheory.KFixIrr.degLE ι P Q R S k).comap (atPl (V` using `fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y)) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, GlobalTheory.RealLift.atPl_tprod]`. Use `GlobalTheory.KFixIrr.tprod_mem_degLE _ ?_` and prove the remaining obligations.

Establish `e1 : ∑ v, (Function.update f w (fockAct2 P Q R S Y (f w)) v).totalDegree = ∑ v, Function.update (fun v => (f v).totalDegree) w (fockAct2 P Q R S Y (f w)).totalDegree v`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `Function.apply_update (fun _ p => MvPolynomial.totalDegree p) f w _ v`. Rewrite using `[e1, Finset.sum_update_of_mem (Finset.mem_univ w)]`. Rewrite `hf` using `[Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ w)]`.

Use `totalDegree_fockAct2_le hY (f w)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `hle hT`.
-/
theorem atPl_fockAct2_mem {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (w : ι) {Y : Mat R S} (hY : IsKC Y) (k : ℕ)
    (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) (hT : T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k) :
    atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y) T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S k := by
  have hle : GlobalTheory.KFixIrr.degLE ι P Q R S k ≤ (GlobalTheory.KFixIrr.degLE ι P Q R S k).comap
      (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, GlobalTheory.RealLift.atPl_tprod]
    refine GlobalTheory.KFixIrr.tprod_mem_degLE _ ?_
    have e1 : ∑ v, (Function.update f w (fockAct2 P Q R S Y (f w)) v).totalDegree =
        ∑ v, Function.update (fun v => (f v).totalDegree) w (fockAct2 P Q R S Y (f w)).totalDegree v := by
      refine Finset.sum_congr rfl fun v _ => ?_
      exact Function.apply_update (fun _ p => MvPolynomial.totalDegree p) f w _ v
    rw [e1, Finset.sum_update_of_mem (Finset.mem_univ w)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ w)] at hf
    have := totalDegree_fockAct2_le hY (f w)
    omega
  exact hle hT

end GlobalTheory.FockLowStab

open GlobalTheory.FockLowStab GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH in
/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B b a' G G₁ H H' _hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM _hM₁ A C Φ hD w Y hY v hv`. Distinguish the cases in `h : Function.Surjective (R.p ∘ₗ Φ) ∧ ∀ Y, Keeps (R.p ∘ₗ Φ) (atPl w (fockAct2 _ _ _ _ Y))`. Take `⟨hb, _, _, _, _⟩` from `hM.triple`. Establish `hdeg` using `GlobalTheory.T.archimedean_theta_polynomial_lift_exists i_actslaws i_derex (i_vacline i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2`. Establish `e : lowPartInf B G.M R.p = (GlobalTheory.KFixIrr.degLE (InfinitePlace F) _ _ _ _ (lowDegInf B G.M R.p)).map (R.p ∘ₗ Φ)`.

Rewrite using `[lowPartInf, hdeg, Submodule.map_comp]`. Rewrite `hv`, the goal using `[e]`. Take `⟨T, hT, rfl⟩` from `hv`. Rewrite using `[fockOp_apply h.1 h.2]`. Conclude with `⟨_, atPl_fockAct2_mem w hY _ T hT, rfl⟩`.

Rewrite using `[fockOp, dif_neg h]`. Conclude with `Submodule.zero_mem _`.
-/
theorem GlobalTheory.FockLowStab.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)),
      Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ lowPartInf B G.M R.p, fockOp (R.p ∘ₗ Φ) w Y v ∈ lowPartInf B G.M R.p := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' _hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM _hM₁ A C Φ hD w Y hY v hv
  by_cases h : Function.Surjective (R.p ∘ₗ Φ) ∧ ∀ Y, Keeps (R.p ∘ₗ Φ) (atPl w (fockAct2 _ _ _ _ Y))
  · obtain ⟨hb, _, _, _, _⟩ := hM.triple
    have hdeg := GlobalTheory.T.archimedean_theta_polynomial_lift_exists i_actslaws i_derex (i_vacline i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ
      hb.cm hb.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2
    have e : lowPartInf B G.M R.p = (GlobalTheory.KFixIrr.degLE (InfinitePlace F) _ _ _ _ (lowDegInf B G.M R.p)).map (R.p ∘ₗ Φ) := by
      rw [lowPartInf, hdeg, Submodule.map_comp]
    rw [e] at hv ⊢
    obtain ⟨T, hT, rfl⟩ := hv
    rw [fockOp_apply h.1 h.2]
    exact ⟨_, atPl_fockAct2_mem w hY _ T hT, rfl⟩
  · rw [fockOp, dif_neg h]
    exact Submodule.zero_mem _
