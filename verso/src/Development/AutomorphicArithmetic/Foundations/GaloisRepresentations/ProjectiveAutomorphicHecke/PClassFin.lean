import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open scoped Pointwise

namespace UpperTheory.Gal.CertificateRingHomMap

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem exists_cover_units (E : Type) [Field E] [NumberField E] (O : Subgroup (Af E)ˣ)
    (hO : IsOpen (O : Set (Af E)ˣ)) :
    ∃ F : Finset (Af E)ˣ, ∀ u ∈ GroundTheory.Global.finiteIntegralUnits E, ∃ f ∈ F, ∃ o ∈ O, u = f * o := by
  obtain ⟨t, ht⟩ := (GroundTheory.Global.isCompact_finiteIntegralUnits E).elim_finite_subcover
    (fun a : (Af E)ˣ => a • (O : Set (Af E)ˣ)) (fun a => hO.smul a)
    (fun c _ => Set.mem_iUnion.2 ⟨c, Set.mem_smul_set.2 ⟨1, one_mem O, mul_one c⟩⟩)
  refine ⟨t, fun u hu => ?_⟩
  obtain ⟨f, hf, huf⟩ := Set.mem_iUnion₂.1 (ht hu)
  obtain ⟨o, ho, rfl⟩ := Set.mem_smul_set.1 huf
  exact ⟨f, hf, o, ho, rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem mem_units_of_valued (E : Type) [Field E] [NumberField E] (u : (Af E)ˣ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : Af E) P) = 1) :
    u ∈ GroundTheory.Global.finiteIntegralUnits E := by
  refine (GroundTheory.Global.mem_finiteIntegralUnits E).2 fun P => ⟨(hu P).le, ?_⟩
  have e : (((u⁻¹ : (Af E)ˣ) : Af E) P) * ((u : Af E) P) = 1 :=
    congrArg (fun t : Af E => t P) (Units.inv_mul u)
  have e2 := congrArg Valued.v e
  rw [map_mul, hu P, mul_one, map_one] at e2
  exact e2.le

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pClassFin_of : ClassFin := by
  intro E _ _ O hO
  classical
  obtain ⟨F, hF⟩ := exists_cover_units E O hO
  let ψ : (Af E)ˣ →* ClassGroup (𝓞 E) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf E).comp GlobalTheory.ClassCover.toIdeles
  let sel : ClassGroup (𝓞 E) → (Af E)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ y, ψ (sel (ψ y)) = ψ y := by
    intro y
    have h : ∃ z, ψ z = ψ y := ⟨y, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨(Finset.univ.image sel ×ˢ F).image (fun p => p.1 * p.2), fun y => ?_⟩
  have hk : ψ ((sel (ψ y))⁻¹ * y) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.ClassCover.eq_diag_mul_of_classOf _ hk
  obtain ⟨f, hf, o, ho, rfl⟩ := hF u (mem_units_of_valued E u hu)
  refine ⟨sel (ψ y) * f, Finset.mem_image.2 ⟨(sel (ψ y), f), Finset.mem_product.2
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hf⟩, rfl⟩, o, ho, k, ?_⟩
  have hy : y = sel (ψ y) * (diagF E k * (f * o)) := by
    rw [show diagF E k * (f * o) = (sel (ψ y))⁻¹ * y from he.symm, mul_inv_cancel_left]
  calc y = sel (ψ y) * (diagF E k * (f * o)) := hy
    _ = sel (ψ y) * f * o * diagF E k := by
      rw [mul_comm (diagF E k), ← mul_assoc, ← mul_assoc]

end UpperTheory.Gal.CertificateRingHomMap
