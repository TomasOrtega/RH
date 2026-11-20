import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameUnimod

/- English proof (translation)
Introduce a local definition for the expression. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isLattice_of_squeeze {E M : Type} [Field E] [NumberField E] [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] {L Λ : Submodule (𝓞 E) M} (hL : Submodule.IsLattice E L) {c : E} (hc : c ≠ 0)
    (h1 : ∀ x ∈ L, c • x ∈ Λ) (h2 : ∀ x ∈ Λ, c • x ∈ L) : Submodule.IsLattice E Λ := by
  let f : M →ₗ[𝓞 E] M := ((c⁻¹ • LinearMap.id : M →ₗ[E] M)).restrictScalars (𝓞 E)
  constructor
  · have hfg : (L.map f).FG := hL.fg.map f
    have hle : Λ ≤ L.map f := fun x hx => ⟨c • x, h2 x hx, by simp [f, smul_smul, hc]⟩
    exact hfg.of_le hle
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have : x = c⁻¹ • (c • x) := by simp [smul_smul, hc]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (h1 x hx))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. Treat this case separately. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coe_span_dualSet {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) :
    (Submodule.span (𝓞 E) (dualSet σ J L) : Set (n → E)) = dualSet σ J L := by
  refine Set.Subset.antisymm (fun y hy => ?_) Submodule.subset_span
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simpa [Formalism.UG.hform] using (algebraMap (𝓞 E) E).range.zero_mem
  | add y z _ _ hy hz =>
    intro x hx
    have : Formalism.UG.hform σ J x (y + z) = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x z := by
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
    rw [this]
    exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : Formalism.UG.hform σ J x (a • y) = algebraMap (𝓞 E) E a * Formalism.UG.hform σ J x y := by
      simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact mul_mem ⟨a, rfl⟩ (hy x hx)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isDefUnimod_of_isBaseFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), V.SigOK → V.IsPosDef → IsBaseFrame V β Λ N → IsDefUnimod D.sp.cm V.gram Λ := by
  intro D V β Λ N hs hp ⟨_, hdual, hN, h1, h2⟩
  obtain ⟨-, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hL : Submodule.IsLattice D.host.E (Formalism.L2.Herm.crdLat V V.L0) :=
    Formalism.MainNotions.StandardLattice.tMap_lattice (Formalism.L2.Herm.crd V) V.L0 V.standardTuple_isLattice
  have hmem : ∀ x, x ∈ Formalism.L2.Herm.crdLat V V.L0 ↔ x ∈ L0c D V := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  refine ⟨Matrix.ext fun i j => (hJ V).1 i j, (hJ V).2.isUnit,
    GlobalTheory.Proof.TotallyDefiniteMass.isTotDef_gram D.sp.cm V hs hp,
    isLattice_of_squeeze hL (Nat.cast_ne_zero.2 hN.ne') (fun x hx => h1 x ((hmem x).1 hx))
      (fun x hx => (hmem _).2 (h2 x hx)), ?_⟩
  rw [← coe_span_dualSet]
  exact congrArg SetLike.coe hdual

end GlobalTheory.BaseFrameUnimod
