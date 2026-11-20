import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealInvariantSesquilinearFormEqSmulInnerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.WeilCoefScalar

/- English proof (translation)
Use `GlobalTheory.MixModel.covolOne_integrableOn hν _ (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, rfl⟩ a`. Establish `e1` using `hf.quasi γ a`. Establish `e2` using `hg.quasi γ a`. Establish `hn : ∀ x, conj (ψ x) * ψ x = 1` using `fun x => by`.

Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]`. Evaluate the numerical expressions. Express the relevant statement in the definitionally equal form `f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)`. Rewrite using `[e1, e2, map_mul]`. Take the linear combination `(f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)`.
-/
theorem integrableOn_mul_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {ν : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕) :
    IntegrableOn (fun w => f w * conj (g w)) 𝓕 ν := by
  refine GlobalTheory.MixModel.covolOne_integrableOn hν _
    (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_
  rintro _ ⟨γ, rfl⟩ a
  have e1 := hf.quasi γ a
  have e2 := hg.quasi γ a
  have hn : ∀ x, conj (ψ x) * ψ x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]; norm_num
  change f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)
  rw [e1, e2, map_mul]
  linear_combination (f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)

end GlobalTheory.WeilCoefScalar

namespace GlobalTheory.WeilCoefScalar

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν`. Establish `hc : (R.cV i).Is` using `hC.models.cV i`. Establish `hW` using `hC.thP.ωP i t`. Establish `hio` using `(hC.thP.ioP i t).1`. Set `J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)` to `(pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))`.

Establish `hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x` using `fun x => rfl`. Establish `hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x)` using `fun x => hC.thP.pt_theta i t _`. Establish `hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν` using `fun x y => integrableOn_mul_conj hW.std (hth y) (hth x) hν`. Set `B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν) (fun x x' y => by`. Simplify using `only [map_add, Pi.add_apply, mul_add]`.

Conclude with `integral_add (hint x y) (hint x' y))`. Use the proof step `(fun a x y => by`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Use the proof step `ring)`. Use the proof step `(fun x y y' => by`. Simplify using `only [map_add, Pi.add_apply, add_mul]`. Conclude with `integral_add (hint x y) (hint x y'))`.

Use the proof step `(fun a x y => by`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Use the proof step `ring)`. Establish `hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν` using `fun x y => rfl`. Establish `hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x)` using `fun u hu x => by`. Rewrite using `[← hJ, ← hJ]`. Conclude with `hio u hu _ x`.

Establish `hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y`. Introduce `u hu x y`. Rewrite using `[hB, hB, ← hom u hu x, ← hom u hu y]`. Conclude with `GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1)) (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)`. Take `⟨z, hz⟩` from `GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv`.

Use `⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩` and prove the remaining obligations. Rewrite using `[hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]`. Rewrite `hw` using `[hJ]`. Establish `h1` using `GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν`. Apply `h1` to reduce the goal to its premises.

Establish `h2` using `hz w w`. Rewrite `h2` using `[hz0, zero_mul, hB]`. Rewrite using `[GlobalTheory.RawLift.thetaIP, ← h2]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[Complex.star_def, mul_comm]`.
-/
theorem wcoef_pure_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by

  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν
  have hc : (R.cV i).Is := hC.models.cV i
  have hW := hC.thP.ωP i t
  have hio := (hC.thP.ioP i t).1
  let J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))
  have hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x := fun x => rfl
  have hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x) := fun x => hC.thP.pt_theta i t _
  have hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν := fun x y =>
    integrableOn_mul_conj hW.std (hth y) (hth x) hν
  let B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν)
      (fun x x' y => by
        simp only [map_add, Pi.add_apply, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
      (fun x y y' => by
        simp only [map_add, Pi.add_apply, add_mul]
        exact integral_add (hint x y) (hint x y'))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
  have hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν := fun x y => rfl
  have hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x) := fun u hu x => by
    rw [← hJ, ← hJ]; exact hio u hu _ x
  have hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y := by
    intro u hu x y
    rw [hB, hB, ← hom u hu x, ← hom u hu y]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1))
      (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv
  refine ⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩
  · rw [hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]
  · rw [hJ] at hw
    have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν
    apply h1
    have h2 := hz w w
    rw [hz0, zero_mul, hB] at h2
    rw [GlobalTheory.RawLift.thetaIP, ← h2]
    congr 1; funext x
    rw [Complex.star_def, mul_comm]

end GlobalTheory.WeilCoefScalar
