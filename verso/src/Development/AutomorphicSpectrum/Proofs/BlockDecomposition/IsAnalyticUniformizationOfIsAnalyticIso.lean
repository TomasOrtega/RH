import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

open WeierstrassCurve GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian

/- English proof (translation)
Distinguish the cases in `hz : z ∈ L.lattice`. Rewrite using `[GlobalTheory.latticePoint_of_mem L hz, toPoint_of_mem hz, map_zero, vcPoint_zero]`. Rewrite using `[GlobalTheory.latticePoint_of_notMem L hz, toPoint_of_notMem hz, GlobalTheory.variableChangePoint_some, vcPoint_some, Affine.Point.some.injEq]`. Establish `hu : (C.u : ℂ) ≠ 0` using `C.u.ne_zero`. Prove the components needed by the constructor for the conclusion.

Simplify using `only [vcX, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [vcY, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem variableChangePoint_latticePoint {X : WeierstrassCurve ℂ} {L : PeriodPair}
    {C : VariableChange ℂ} (h : C • X = GlobalTheory.latticeCurve L) (h' : C⁻¹ • weierstrassCurve L = X)
    (z : ℂ) :
    GlobalTheory.variableChangePoint C h (GlobalTheory.latticePoint L z) = vcPoint C⁻¹ h' (toPoint L z) := by
  by_cases hz : z ∈ L.lattice
  · rw [GlobalTheory.latticePoint_of_mem L hz, toPoint_of_mem hz, map_zero, vcPoint_zero]
  · rw [GlobalTheory.latticePoint_of_notMem L hz, toPoint_of_notMem hz, GlobalTheory.variableChangePoint_some,
      vcPoint_some, Affine.Point.some.injEq]
    have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
    constructor
    · simp only [vcX, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring
    · simp only [vcY, VariableChange.inv_def, inv_inv, Units.val_inv_eq_inv_val]
      field_simp
      ring

/- English proof (translation)
Take `⟨L, C, h⟩` from `GlobalTheory.exists_variableChange_eq_latticeCurve X`. Take `⟨α, hα, hΛ, hz⟩` from `hξ.exists_mul h`. Establish `e : GlobalTheory.latticeCurve L = weierstrassCurve L`. Simplify using `[GlobalTheory.latticeCurve, weierstrassCurve, neg_div]`. Establish `h' : C⁻¹ • weierstrassCurve L = X`.

Rewrite using `[← e, ← h, inv_smul_smul]`. Establish `hΛ' : ∀ z, z ∈ idealLattice (algebraMap K ℂ) 𝔞 ↔ α * z ∈ L.lattice` using `fun z => by`. Rewrite using `[← hΛ]`. Both sides reduce to the same expression. Establish `hf` using `((isAnalyticUniformization_toPointHom L).comp_mul hα hΛ').vcPoint C⁻¹ h'`.

Use `hf using 1` and compare the differences between its conclusion and the goal. Use extensionality with `z`. Simplify using `only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply, AddMonoidHom.coe_mulLeft]`. Conclude with `(hz z).trans (variableChangePoint_latticePoint h h' _)`.
-/
theorem isAnalyticUniformization_of_isAnalyticIso {K : Type} [Field K] [NumberField K]
    [IsTotallyComplex K] [Algebra K ℂ] (_h2 : Module.finrank ℚ K = 2) (X : WeierstrassCurve ℂ)
    [X.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (_h𝔞 : 𝔞 ≠ 0)
    (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub 𝔞) ≃+ X.toAffine.Point)
    (hξ : GlobalTheory.EllipticCM.IsAnalyticIso ξ) :
    GroundTheory.Global.Elliptic.IsAnalyticUniformization
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) 𝔞)
      (ξ.toAddMonoidHom.comp (QuotientAddGroup.mk' _)) := by
  obtain ⟨L, C, h⟩ := GlobalTheory.exists_variableChange_eq_latticeCurve X
  obtain ⟨α, hα, hΛ, hz⟩ := hξ.exists_mul h
  have e : GlobalTheory.latticeCurve L = weierstrassCurve L := by
    simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]
  have h' : C⁻¹ • weierstrassCurve L = X := by
    rw [← e, ← h, inv_smul_smul]
  have hΛ' : ∀ z, z ∈ idealLattice (algebraMap K ℂ) 𝔞 ↔ α * z ∈ L.lattice := fun z => by
    rw [← hΛ]
    rfl
  have hf := ((isAnalyticUniformization_toPointHom L).comp_mul hα hΛ').vcPoint C⁻¹ h'
  convert hf using 1
  ext z
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, vcPointEquiv_apply,
    AddMonoidHom.coe_mulLeft]
  exact (hz z).trans (variableChangePoint_latticePoint h h' _)

end GlobalTheory.CompanionTheory.EllipticCM
