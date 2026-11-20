import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceLeSpanPureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceEndomorphismPreservesTorusWeiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceCoefficientSpaceEqExtremalTensorLineStatement
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoefSchur

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem polyAction_ten (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    actP lam h (ten f) = ten fun τ => sqAct K n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)).1
  simp only [actP, ten, detTwK, trAct, sqAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
theorem natW_anti {n : ℕ} (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ten_ext_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (ten fun τ => extremal K n (lam τ)) ∈ VV K lam :=
  Submodule.subset_span ⟨fun τ => extremal K n (lam τ),
    fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (natW_anti (lam τ)), rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem endo_scalar : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g : Module.End K (VV K lam)),
    (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∃ a : K, ∀ v, g v = a • v := by
  intro K _ _ ι _ n lam g hg
  set v0 : VV K lam := ⟨_, ten_ext_mem K lam⟩ with hv0
  have hw0 := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).1
  have hgw := GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight K lam g hg v0 hw0
  obtain ⟨a, ha⟩ := (GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine K lam).2 _ (g v0).2 hgw
  have ha' : g v0 = a • v0 := Subtype.ext ha
  refine ⟨a, ?_⟩
  let W : Submodule K (Pol K ι n) := Submodule.map (VV K lam).subtype (LinearMap.ker (g - a • LinearMap.id))
  have hS : ∀ τ, nablaSq K n (lam τ) ≤ Submodule.span K (Set.range fun x : GL (Fin n) K => sqAct K n (lam τ) x (extremal K n (lam τ))) :=
    fun τ => GlobalTheory.T.dualWeylModule_le_span_extremalTranslates K n (lam τ)
  have hle := GlobalTheory.T.weylTensorCoefSpace_le_span_pure_tensors K lam _ hS
  have hW : VV K lam ≤ W := by
    refine hle.trans (Submodule.span_le.2 ?_)
    rintro P ⟨f, hf, rfl⟩
    choose h hh using hf
    have e : ten f = ten fun τ => sqAct K n (lam τ) (h τ) (extremal K n (lam τ)) := by
      congr 1; funext τ; exact (hh τ).symm
    refine ⟨rhoK lam h v0, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hg, ha', map_smul, sub_self]
    · rw [e, ← polyAction_ten]; rfl
  intro v
  obtain ⟨w, hw, hwv⟩ := hW v.2
  have : w = v := Subtype.ext hwv
  subst this
  simpa [sub_eq_zero] using hw

end GlobalTheory.CoefSchur
