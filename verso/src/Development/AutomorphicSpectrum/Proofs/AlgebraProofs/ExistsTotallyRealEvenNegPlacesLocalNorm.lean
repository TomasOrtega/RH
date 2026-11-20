import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FgInfRestrictScalarsOfIntegers

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_smul_mem_of_mem_span_val {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {V : Type} [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) {u : V}
    (hu : u ∈ Submodule.span C (L : Set V)) : ∃ c : C, c ≠ 0 ∧ c • u ∈ L := by
  have key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L := by
    intro a b x hb hab hx
    have hvb : 0 < v b := (Valuation.pos_iff v).2 hb
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one hvb).2 hab
    obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
    have h2 : a • x = o • (b • x) := by
      rw [← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]
    rw [h2]
    exact L.smul_mem o hx
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    rcases le_total (v a) (v b) with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩
    · exact ⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩
  | smul d x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by simp [hd]⟩
    · exact ⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem latIn_isLattice : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V), L.FG → U ≤ Submodule.span C (L : Set V) → (latIn L U).IsLattice C := by
  intro C _ v O _ _ hv V _ _ _ _ L U hL hU
  have hfg := GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (U.subtype.restrictScalars O) := Subtype.val_injective
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj
    convert hfg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  · rw [eq_top_iff]
    intro u _
    obtain ⟨c, hc, hcu⟩ := exists_smul_mem_of_mem_span_val hv L (hU u.2)
    have h1 : c • u ∈ Submodule.span C (latIn L U : Set U) := Submodule.subset_span hcu
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

end GlobalTheory.CompanionTheory.Ar.HT
