import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjectiveDetPowMulDualWeyl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylInvariantPairingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorProductNondegeneratePairingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.AutPairing

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `n ι _ _ mu sh lam hlam`. Establish `hE : ∀ τ, ∃ e : nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v, (e (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) : MvPolynomial (Fin n × Fin n) ℂ) = detPow …` using `n) (g : Matrix (Fin n) (Fin n) ℂ).transpose (e v : MvPolynomial (Fin n × Fin n) ℂ) := fun τ => GlobalTheory.Branching.exists_surjective_detPowMul_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hlam τ a)`. Use `choose e he_surj he_eq using hE`. Establish `hF : ∀ τ, ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ, (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.Cohomolog …` using `n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v) (Formalism.UG.dwAct ℂ n n g u) = b v u := fun τ => GlobalTheory.T.dual_weyl_invariant_pairing n (Formalism.CohomologicalDescent.LD.res n (mu τ))`. Use `choose b hb_sep hb_inv using hF`.

Set `bt : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) →ₗ[ℂ] ℂ` to `fun τ => ((b τ).compl₂ (Submodule.subtype _)).comp ((Submodule.subtype _).comp (e τ))`. Establish `bt_apply : ∀ τ v u, bt τ v u = b τ (e τ v : MvPolynomial (Fin n × Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ)` using `fun _ _ _ => rfl`. Establish `bt_sep : ∀ τ u, u ≠ 0 → ∃ v, bt τ v u ≠ 0`. Introduce `τ u hu`. Establish `hu' : (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0` using `fun h => hu (Subtype.ext h)`.

Take `⟨v, hv, hne⟩` from `hb_sep τ u u.2 hu'`. Take `⟨w, hw⟩` from `he_surj τ ⟨v, hv⟩`. Conclude with `⟨w, by rw [bt_apply, hw]; exact hne⟩`. Establish `bt_inv : ∀ τ (g : GL (Fin n) ℂ) v u, bt τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) (Formalism.UG.dualWeylRep ℂ n n _ g u) = detPow ℂ n g (sh τ) * bt τ v u`. Introduce `τ g v u`.

Rewrite using `[bt_apply, bt_apply, he_eq]`. Establish `h1 : (Formalism.UG.dualWeylRep ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) g u : MvPolynomial (Fin n × Fin n) ℂ) = Formalism.UG.dwAct ℂ n n g u` using `rfl`. Rewrite using `[h1, map_smul, LinearMap.smul_apply, hb_inv, smul_eq_mul]`. Use `haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := (GlobalTheory.T.weight_module_finite_continuous n ι mu sh).1`. Take `⟨Bm, hBm, hBm_sep⟩` from `GlobalTheory.T.tensor_product_nondegenerate_pairing ι (fun τ => nablaSq ℂ n (lam τ)) (fun τ => Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) bt bt_sep`.

Take `⟨B, hB, -⟩` from `GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm`. Use `⟨B, fun u hu => ?_, fun g => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hBm_sep u hu`. Conclude with `⟨GlobalTheory.CoefIrred.tenMul lam v, by rw [hB]; exact hv⟩`. Establish `hc : ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) * ∏ τ, detPow ℂ n (g τ) (sh τ) = 1`.

Simplify using `only [detPow]`. Rewrite using `[← Units.coe_prod, ← Units.val_mul, ← Finset.prod_mul_distrib]`. Simplify using `[← zpow_add]`. Establish `hpure : ∀ x y, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x)) (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ y)) = B (GlobalTheory.CoefIrred.tenMul lam x) (PiTensorProduct.tprod ℂ y)`. Introduce `x y`.

Rewrite using `[GlobalTheory.DefU.rhoK_tenMul, hB, hB, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hBm, hBm, smul_eq_mul]`. Repeatedly rewrite using `[bt_inv]`. Rewrite using `[Finset.prod_mul_distrib, ← mul_assoc, hc, one_mul]`. Establish `hten : ∀ x u, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x)) (wtOp ℂ n mu sh g u) = B (GlobalTheory.CoefIrred.tenMul lam x) u`. Introduce `x u`.

Proceed by induction on `u using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c y => rw [map_smul, map_smul, map_smul, hpure]`. Consider the case `add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']`. Establish `h1 : ∀ x, ((B.comp (Formalism.L2.DIV.rhoK lam g)).compl₂ (wtOp ℂ n mu sh g)) (GlobalTheory.CoefIrred.tenMul lam x) = Bm x`. Introduce `x`.

Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.compl₂_apply, LinearMap.comp_apply, hten, hB]`. Establish `h2` using `(GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm).unique h1 hB`. Introduce `v u`. Use `LinearMap.congr_fun (LinearMap.congr_fun h2 v) u` as an intermediate fact.

Simplify using `using this`.
-/
theorem exists_invariant_pairing : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (lam : ι → DomWeight n), (∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ) →
    ∃ B : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, u ≠ 0 → ∃ v, B v u ≠ 0) ∧
      ∀ (g : ι → GL (Fin n) ℂ) v u, B (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = B v u := by
  intro n ι _ _ mu sh lam hlam
  have hE : ∀ τ, ∃ e : nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)),
      Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v,
        (e (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) : MvPolynomial (Fin n × Fin n) ℂ) =
          detPow ℂ n g (sh τ) • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
            (e v : MvPolynomial (Fin n × Fin n) ℂ) :=
    fun τ => GlobalTheory.Branching.exists_surjective_detPowMul_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hlam τ a)
  choose e he_surj he_eq using hE
  have hF : ∀ τ, ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), u ≠ 0 →
        ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
        (Formalism.UG.dwAct ℂ n n g u) = b v u :=
    fun τ => GlobalTheory.T.dual_weyl_invariant_pairing n (Formalism.CohomologicalDescent.LD.res n (mu τ))
  choose b hb_sep hb_inv using hF
  let bt : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) →ₗ[ℂ] ℂ :=
    fun τ => ((b τ).compl₂ (Submodule.subtype _)).comp ((Submodule.subtype _).comp (e τ))
  have bt_apply : ∀ τ v u, bt τ v u =
      b τ (e τ v : MvPolynomial (Fin n × Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) := fun _ _ _ => rfl
  have bt_sep : ∀ τ u, u ≠ 0 → ∃ v, bt τ v u ≠ 0 := by
    intro τ u hu
    have hu' : (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
    obtain ⟨v, hv, hne⟩ := hb_sep τ u u.2 hu'
    obtain ⟨w, hw⟩ := he_surj τ ⟨v, hv⟩
    exact ⟨w, by rw [bt_apply, hw]; exact hne⟩
  have bt_inv : ∀ τ (g : GL (Fin n) ℂ) v u,
      bt τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) (Formalism.UG.dualWeylRep ℂ n n _ g u) =
        detPow ℂ n g (sh τ) * bt τ v u := by
    intro τ g v u
    rw [bt_apply, bt_apply, he_eq]
    have h1 : (Formalism.UG.dualWeylRep ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) g u : MvPolynomial (Fin n × Fin n) ℂ) =
        Formalism.UG.dwAct ℂ n n g u := rfl
    rw [h1, map_smul, LinearMap.smul_apply, hb_inv, smul_eq_mul]
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :=
    (GlobalTheory.T.weight_module_finite_continuous n ι mu sh).1
  obtain ⟨Bm, hBm, hBm_sep⟩ := GlobalTheory.T.tensor_product_nondegenerate_pairing ι (fun τ => nablaSq ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) bt bt_sep
  obtain ⟨B, hB, -⟩ := GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm
  refine ⟨B, fun u hu => ?_, fun g => ?_⟩
  · obtain ⟨v, hv⟩ := hBm_sep u hu
    exact ⟨GlobalTheory.CoefIrred.tenMul lam v, by rw [hB]; exact hv⟩
  · have hc : ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) *
        ∏ τ, detPow ℂ n (g τ) (sh τ) = 1 := by
      simp only [detPow]
      rw [← Units.coe_prod, ← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have hpure : ∀ x y, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x))
        (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ y)) = B (GlobalTheory.CoefIrred.tenMul lam x) (PiTensorProduct.tprod ℂ y) := by
      intro x y
      rw [GlobalTheory.DefU.rhoK_tenMul, hB, hB, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hBm, hBm, smul_eq_mul]
      simp_rw [bt_inv]
      rw [Finset.prod_mul_distrib, ← mul_assoc, hc, one_mul]
    have hten : ∀ x u, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x)) (wtOp ℂ n mu sh g u) =
        B (GlobalTheory.CoefIrred.tenMul lam x) u := by
      intro x u
      induction u using PiTensorProduct.induction_on with
      | smul_tprod c y => rw [map_smul, map_smul, map_smul, hpure]
      | add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']
    have h1 : ∀ x, ((B.comp (Formalism.L2.DIV.rhoK lam g)).compl₂ (wtOp ℂ n mu sh g)) (GlobalTheory.CoefIrred.tenMul lam x) = Bm x := by
      intro x
      refine LinearMap.ext fun u => ?_
      rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hten, hB]
    have h2 := (GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm).unique h1 hB
    intro v u
    have := LinearMap.congr_fun (LinearMap.congr_fun h2 v) u
    simpa using this

end GlobalTheory.AutPairing

end
