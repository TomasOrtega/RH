import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : Function.Injective
      (LinearMap.lTensor V (PD.ι.toLinearMap.restrictScalars Qp)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ PD.ι_inj
  exact h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.
-/
theorem ιV_actVB (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem map_Dcris_le (ρ : Representation LL G V) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) ≤ DdR PD ρ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [← ιV_actVB, hx g]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem DdR_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(DdR PD ρ) := by
  by_cases hV : finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    have h0 : ∀ x : V ⊗[Qp] BdR, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
      | add a c ha hc => rw [ha, hc, add_zero]
    haveI : Subsingleton ↥(DdR PD ρ) :=
      ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Dcris_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := DdR_finite PD ρ h
  haveI : FiniteDimensional LL ↥((Dcris PD ρ).map (ιV PD (LL := LL) (V := V))) :=
    Submodule.finiteDimensional_of_le (map_Dcris_le PD ρ)
  exact Module.Finite.equiv
    (Submodule.equivMapOfInjective _ (ιV_injective PD) (Dcris PD ρ)).symm

end Generic

end GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem GlobalTheory.DcrisFin.dcris_finite_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsDR (P.PD K) ρ → Module.Finite ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI := (P.PD K).finK
  exact GlobalTheory.DcrisFin.Dcris_finite (P.PD K) ρ h
