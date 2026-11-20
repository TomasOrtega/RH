import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeylStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftNabStdMemLatN
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

/- English proof (translation)
Unfold `detPol`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `a s`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
theorem detPol_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    MvPolynomial.map f (detPol R n) = detPol S n := by
  unfold detPol
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `hn : 0 < n` using `Nat.lt_of_le_of_lt (Nat.zero_le _) a.2`. Set `m : Fin n` to `⟨n - 1, by omega⟩`. Establish `h1 : (lamW τ a : ℤ) = (lam τ).w a + c τ` using `hS τ a`. Establish `h2 : (lamW τ (n - 1) : ℤ) = (lam τ).w m + c τ` using `hS τ m`.

Establish `hle : (lam τ).w m ≤ (lam τ).w a` using `(lam τ).anti (Fin.le_def.2 (by simp only [m]; omega))`. Establish `hd : (lam τ).detShift = (lam τ).w m` using `by simp [DomWeight.detShift, hn, m]`. Use `show lamW τ a = ((lam τ).w a - (lam τ).detShift).toNat + lamW τ (n - 1)`. Rewrite using `[hd]`. Establish `h3 : ((((lam τ).w a - (lam τ).w m).toNat : ℕ) : ℤ) = (lam τ).w a - (lam τ).w m` using `Int.toNat_of_nonneg (by omega)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem res_eq_natW_add {ι : Type} {n : ℕ} (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ)
    (hS : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  let m : Fin n := ⟨n - 1, by omega⟩
  have h1 : (lamW τ a : ℤ) = (lam τ).w a + c τ := hS τ a
  have h2 : (lamW τ (n - 1) : ℤ) = (lam τ).w m + c τ := hS τ m
  have hle : (lam τ).w m ≤ (lam τ).w a := (lam τ).anti (Fin.le_def.2 (by simp only [m]; omega))
  have hd : (lam τ).detShift = (lam τ).w m := by simp [DomWeight.detShift, hn, m]
  show lamW τ a = ((lam τ).w a - (lam τ).detShift).toNat + lamW τ (n - 1)
  rw [hd]
  have h3 : ((((lam τ).w a - (lam τ).w m).toNat : ℕ) : ℤ) = (lam τ).w a - (lam τ).w m := Int.toNat_of_nonneg (by omega)
  omega

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN`.
-/
theorem lift_nabStd_mem_latN : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW :=
  _root_.UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN

end GlobalTheory.FrameRead
