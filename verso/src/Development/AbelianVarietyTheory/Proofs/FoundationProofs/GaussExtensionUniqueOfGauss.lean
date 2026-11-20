import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.BertiniNoether

/- English proof (translation)
Introduce `F _ _ _ _ L _ _ t ht hfin`. Take `⟨Φ, ω, hmon, hirr, hroot, hspan⟩` from `GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive t ht hfin`. Take `⟨s, Ψ₀, hΨ₀, hgr⟩` from `GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation Φ hmon hirr`. Take `⟨S, hS⟩` from `GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s`. Use `⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩` and prove the remaining obligations.

Establish `hcl : Subring.closure (s : Set F) ≤ V.toSubring` using `(Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)`. Set `ι : Subring.closure (s : Set F) →+* V` to `{ toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Establish `hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype` using `RingHom.ext fun _ => rfl`. Use `set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef`. Establish `hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ`.

Rewrite using `[hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]`. Establish `hinj : Function.Injective (Polynomial.mapRingHom V.subtype)` using `Polynomial.map_injective _ (fun a b h => Subtype.ext h)`. Establish `hΨmon : Ψ.Monic` using `Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)`. Establish `hdeg : Ψ.natDegree = Φ.natDegree`. Rewrite using `[← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]`.

Establish `hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0`. Introduce `k _ φ A B hA hB hAB`. Use `hgr k (φ.comp ι) A B hA hB ?_` and prove the remaining obligations. Rewrite using `[hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]`. Establish `hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V`.

Introduce `i j`. Rewrite using `[← hΨ]`. Simplify using `only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]`. Conclude with `((Ψ.coeff i).coeff j).2`. Establish `hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0`.

Rewrite using `[hΨ]`. Conclude with `hroot`. Establish `key : ∀ W : ValuationSubring L, Gauss t V W → ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits`. Introduce `W hW R hR`. Conclude with `GlobalTheory.gaussExtension_coeff_mem_nonunits t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)`.

Conclude with `le_antisymm (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ h₁ h₂ (key W₁ h₁)) (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ h₂ h₁ (key W₂ h₂))`.
-/
theorem gauss_extension_unique_of_gauss : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have key : ∀ W : ValuationSubring L, Gauss t V W →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.gaussExtension_coeff_mem_nonunits t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ h₁ h₂ (key W₁ h₁))
    (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ h₂ h₁ (key W₂ h₂))

end GlobalTheory.BertiniNoether
