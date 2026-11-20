import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.GoodDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare Formalism.L2.DIV GlobalTheory.BI

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isChar_inv {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem goodIdempotent_coeff_inv_eq_coeff {D : D7} {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (h : G0g D.nd) :
    D.ntypes.e0.coeff h⁻¹ = D.ntypes.e0.coeff h := by
  obtain ⟨x, rfl⟩ := pull_bijective.2 h
  have e : (pull x)⁻¹ = pull x⁻¹ := rfl
  rw [e, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ x x⁻¹
    (fun v _ => by rw [Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem goodStable_of_coeff {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hirr : ∀ χ ∈ X, IsAbsIrrChar χ)
    (hsym : ∀ g, (idemOf X).coeff g⁻¹ = (idemOf X).coeff g) : GoodStable X := by
  classical
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf emb X hirr X
    (fun ψ g => emb (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hirr ψ hψ)
      exact isChar_inv ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply emb.injective
  simpa using hψe g⁻¹

end GlobalTheory.Mem.R3.GoodDual

open GlobalTheory.Mem.R3.GoodDual in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.Mem.Top.Bl.goodStable_atDat : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => GoodStable (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.X := by
  intro hG _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z hT _ _ _ => ?_
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hT).2.1
  show GoodStable z.Xg
  refine goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
  apply (w.st Z).B.embLL.injective
  rw [z.good.2, z.good.2, map_inv, goodIdempotent_coeff_inv_eq_coeff hI]
