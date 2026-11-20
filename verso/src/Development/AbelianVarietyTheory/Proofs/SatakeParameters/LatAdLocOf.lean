import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpEqImage
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

/- English proof (translation)
Introduce `F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v`. Use `letI : StarRing E := starRingOfComm`. Use `set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) := Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY`. Use `set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v := ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf`. Establish `hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f`.

Rewrite using `[hY]`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F, (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) = ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ (fun k => (A.eQ v).symm (A.ph v (u k)))`. Introduce `u`.

Rewrite using `[hfac]`. Use function extensionality and compare the values at `k`. Conclude with `RingHom.map_mulVec f Y u k`. Use extensionality with `z'`. Rewrite using `[locSp_eq_image A hS hI v, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzz⟩`. Rewrite `hz` using `[GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]`. Use `set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu`. Use `⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `hzu : z = Y *ᵥ u`. Rewrite using `[hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Use `show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'`. Rewrite using `[← hmv, ← hzu]`. Use function extensionality and compare the values at `k`.

Conclude with `hzz k`. Introduce and unpack `⟨w, hw, hwz⟩`. Take `⟨u, hu, huw⟩` from `(locSp_eq_image A hS hI v Lb w).1 hw`. Use `⟨Y *ᵥ u, ?_, ?_⟩` and prove the remaining obligations. Establish `hback : Units.val ((bc (prV (E` using `E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ (Y *ᵥ u) = u := by`.

Rewrite using `[hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Rewrite using `[GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]`. Rewrite using `[hback]`. Conclude with `hu`. Introduce `k`.

Establish `hw' : w = fun k => (A.eQ v).symm (A.ph v (u k))` using `funext fun k => (huw k).symm`. Substitute `hwz` using the available equality. Substitute `hw'` using the available equality. Conclude with `congrFun (hmv u) k`.
-/
theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
