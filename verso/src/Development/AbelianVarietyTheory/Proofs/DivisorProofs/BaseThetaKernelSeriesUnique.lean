import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.BaseKernelUniq

variable {D : D7}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem res_unique {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP => (GlobalTheory.HeckeParts.idem_unique V (hes PP hP) (hes' PP hP)).symm

/- English proof (translation)
Replace the relevant objects with their definitions. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem omegaQ_congr {a b : ℕ} {Q : Finset (Pl D.host.E)} {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) (r : ℕ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ Q r ξ' k y := by
  unfold omegaQ
  split_ifs with hy
  · exact Finset.prod_congr rfl fun PP _ => by rw [hξ PP.1 PP.2]
  · rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem thPVec_unique {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) (h' : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f')
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) : f = f' := by
  obtain ⟨-, e, he, hT⟩ := h
  obtain ⟨-, e', he', hT'⟩ := h'
  obtain rfl := idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT
  rw [hall Tm hTm, hT'.2 Tm hTm]
  congr 1
  funext x
  simp only [omegaQ_congr hξ]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem baseKernelUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → BaseKernelUnique R i v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i v _ _ ω φ ω' φ' hk hk'
  obtain ⟨χ, ξR, hχ, hres, hω, hv⟩ := hk
  obtain ⟨χ', ξR', hχ', hres', hω', hv'⟩ := hk'
  obtain rfl : χ = χ' := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 χ χ' _ hχ hχ'
  obtain rfl : φ = φ' := thPVec_unique hv hv' fun PP hP => res_unique (hres PP hP) (hres' PP hP)
  have hθφ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  have hinf : IsInfFam R.θ := hv.1.2.inf
  funext h w u g
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hω.std _ _ _ _ ω ω' hω hω' (h, g) _
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hinf _ _ _ _ hθφ _)) 0

end GlobalTheory.BaseKernelUniq

end
