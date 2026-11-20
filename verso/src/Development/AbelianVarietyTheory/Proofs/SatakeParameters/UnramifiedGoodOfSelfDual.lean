import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.UnrTwist

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    UpperTheory.V.Af.tw (UpperTheory.V.Af.tw r μ) μ⁻¹ = r := by
  ext s i j
  simp [UpperTheory.V.Af.tw_val, smul_smul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem algSat_eq' (n q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [UpperTheory.V.Af.algSat, Multiset.bind_singleton, Multiset.map_map]

end GlobalTheory.RoadU.UnrTwist

open GlobalTheory.RoadU.UnrTwist in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
-/
theorem GlobalTheory.RoadU.holdsS_good_unr : Inputs → SphericalLevelCondition .csd .unr → SphericalLevelCondition .good .unr := by
  intro _ hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w hw B hB hl
  obtain ⟨κ, m, hκ, hu, hS'⟩ := GlobalTheory.GoodCsdTwist.exists_goodCsd_twist GlobalTheory.automorphicFormsFiniteGL E l a ha π χ hS w hw
  obtain ⟨art, hart, H⟩ := GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter GlobalTheory.globalArtinReciprocity_holds E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := H l ι κ m (isAlgPos_of_isAlg hκ)
  have hrv : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) :=
    Units.continuous_val.comp hr.1
  have htv : Continuous fun g => ((UpperTheory.V.Af.tw r μ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμc).smul hrv
  have htc : Continuous (UpperTheory.V.Af.tw r μ) := by
    refine Units.continuous_iff.2 ⟨htv, ?_⟩
    simp only [← map_inv]
    exact htv.comp continuous_inv
  have hT : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨htc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have hB' : (CG.mk (π.twist κ)).HasSat w (B.map (· * κ.val w)) := by
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B hu hB
  have hc : UpperTheory.V.Af.FrobEig ι (UpperTheory.V.Af.tw r μ) w
      (UpperTheory.V.Af.algSat a (normV w) (B.map (· * κ.val w))) :=
    hcsd E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hS' (UpperTheory.V.Af.tw r μ) hT w hw _ hB' hl
  have hce : UpperTheory.V.Af.Bc.CharEig ι μ⁻¹ w ((κ.val w : ℂ))⁻¹ := by
    refine fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [MonoidHom.inv_apply, (hμ.unr_iff hart (Or.inl hl) hA).2 hu s hs, inv_one]
    · rw [MonoidHom.inv_apply, map_inv, inv_inv, hμ.frob_unr hart (Or.inl hl) hu hA hσ, map_inv₀, RingEquiv.apply_symm_apply]
  have h2 := UpperTheory.frobenius_eigenvalues_twist E Ω l ι a _ μ⁻¹ w _ _ hc hce
  rw [tw_tw_inv] at h2
  convert h2 using 1
  simp only [algSat_eq', Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  field_simp
