import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClosedPt

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts TopologicalSpace

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_residue_eval : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ),
    LocallyOfFiniteType p → ∀ (B : LB Y), B.IsLB → ∀ z : Y, IsClosed ({z} : Set Y) →
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (e : B.Sec →+ K),
      (∀ (a : F) (s : B.Sec), e (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a • s) = algebraMap F K a * e s) ∧
      (∀ s : B.Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → e s ≠ 0) ∧
      ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∃ (y : GlobalTheory.CxPts p σ) (i : B.ι),
        y.1 (IsLocalRing.closedPoint ℂ) = z ∧ ∀ s : B.Sec, GlobalTheory.CxPts.secVal p σ s i y = τ (e s) := by
  intro F _ Y p σ hp B hB z hz
  obtain ⟨i, hzi⟩ : ∃ i, z ∈ B.U i := Opens.mem_iSup.1 (by rw [hB.cover]; trivial)
  obtain ⟨U, hU, hzU, hUi⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hzi
  replace hU : IsAffineOpen U := hU
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hftA : Algebra.FiniteType F Γ(Y, U) := hft
  set x0 := hU.primeIdealOf ⟨z, hzU⟩ with hx0
  have hfx : hU.fromSpec x0 = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hcl : IsClosed ({x0} : Set (PrimeSpectrum Γ(Y, U))) := by
    have h1 : IsClosed (hU.fromSpec.base ⁻¹' {z}) := hz.preimage hU.fromSpec.base.hom.continuous
    have h2 : hU.fromSpec.base ⁻¹' {z} = {x0} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hq
        exact hU.fromSpec.isOpenEmbedding.injective (hq.trans hfx.symm)
      · rintro rfl; exact hfx
    rw [h2] at h1
    exact h1
  have hmax : x0.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hcl
  let P := x0.asIdeal
  letI : Field (Γ(Y, U) ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType F (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  have hfin : Module.Finite F (Γ(Y, U) ⧸ P) := finite_of_finite_type_of_isJacobsonRing F _
  have hmem : ∀ f : Γ(Y, U), z ∈ Y.basicOpen f ↔ f ∉ P := by
    intro f
    have h1 : x0 ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen f ↔ hU.fromSpec x0 ∈ Y.basicOpen f := Iff.rfl
    rw [hfx, hU.fromSpec_preimage_basicOpen] at h1
    exact h1.symm.trans (PrimeSpectrum.mem_basicOpen _ _)
  let e : B.Sec →+ Γ(Y, U) ⧸ P :=
    { toFun := fun s => Ideal.Quotient.mk P (resG Y hUi (s.f i))
      map_zero' := by simp
      map_add' := fun s t => by simp only [GlobalTheory.LB.add_f, map_add] }
  refine ⟨Γ(Y, U) ⧸ P, inferInstance, inferInstance, hfin, e, ?_, ?_, ?_⟩
  · intro a s
    change Ideal.Quotient.mk P (resG Y hUi ((algX p ⊤ a • s).f i)) = _ * Ideal.Quotient.mk P _
    have hres : resG Y (hUi.trans le_top) (algX p ⊤ a) = algX p U a :=
      RingHom.congr_fun (GlobalTheory.TopForm.resG_comp_algX p (hUi.trans le_top)) a
    rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LB.resG_resG, hres]
    rfl
  · intro s hs
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hs
    have hki : z ∈ B.U i ⊓ B.U k := ⟨hzi, Y.basicOpen_le _ hk⟩
    have hrel := GlobalTheory.LB.sec_rel s i k (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) inf_le_right le_rfl
    have h1 : z ∈ Y.basicOpen (resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i)) := by
      rw [hrel, Scheme.basicOpen_mul, Y.basicOpen_of_isUnit
        ((B.g i k).isUnit.map (resG Y le_rfl))]
      refine ⟨hki, ?_⟩
      have : resG Y (inf_le_right : B.U i ⊓ B.U k ≤ B.U k) (s.f k) =
          Y.presheaf.map (homOfLE (inf_le_right : B.U i ⊓ B.U k ≤ B.U k)).op (s.f k) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hki, hk⟩
    have h2 : z ∈ Y.basicOpen (s.f i) := by
      have : resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i) =
          Y.presheaf.map (homOfLE (inf_le_left : B.U i ⊓ B.U k ≤ B.U i)).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res] at h1
      exact h1.2
    have h3 : z ∈ Y.basicOpen (resG Y hUi (s.f i)) := by
      have : resG Y hUi (s.f i) = Y.presheaf.map (homOfLE hUi).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hzU, h2⟩
    change Ideal.Quotient.mk P _ ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact (hmem _).1 h3
  · intro τ hτ
    let φ : Γ(Y, U) →+* ℂ := τ.comp (Ideal.Quotient.mk P)
    have hφ : ∀ a, φ (algX p U a) = σ a := fun a => by
      rw [← hτ]; rfl
    refine ⟨ofHom hU φ hφ, i, ?_, fun s => ?_⟩
    · have hker : RingHom.ker φ = P := by
        rw [RingHom.ker_comp_of_injective _ τ.injective]
        exact Ideal.mk_ker
      have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = x0 := by
        apply PrimeSpectrum.ext
        change Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = P
        rw [IsLocalRing.maximalIdeal_eq_bot]
        exact hker
      change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ)) = z
      rw [hpt, hfx]
    · rw [secVal_apply, ← ev_res hUi (ofHom_mem hU φ hφ), ev_ofHom]
      rfl

end GlobalTheory.CompanionTheory.Ar.ClosedPt
