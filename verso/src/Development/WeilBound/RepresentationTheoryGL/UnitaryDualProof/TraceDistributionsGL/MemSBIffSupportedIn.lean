import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo

noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def cutL {n : ℕ} (U : Set k) : (Mx k n → ℂ) →ₗ[ℂ] (GL (Fin (n + 1)) k → ℂ) where
  toFun ψ x := if (x.val).det ∈ U then ψ x.val else 0
  map_add' ψ₁ ψ₂ := funext fun x => by
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c ψ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cutL_apply {n : ℕ} (U : Set k) (ψ : Mx k n → ℂ) (x : GL (Fin (n + 1)) k) :
    cutL U ψ x = if (x.val).det ∈ U then ψ x.val else 0 := by
  classical
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mem_SB_iff_supportedIn {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ f ∈ supportedIn (Set.univ : Set X) := by
  constructor
  · intro h
    exact ⟨h, Set.subset_univ _⟩
  · intro h
    exact h.1

/- English proof (translation)
Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cutL_mem {n : ℕ} (U : Set k) (hU : IsClopen U) (h0 : (0 : k) ∉ U) {ψ : Mx k n → ℂ}
    (hψ : ψ ∈ SB (Mx k n)) : cutL U ψ ∈ SB (GL (Fin (n + 1)) k) := by
  have h := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.cutFun_mem U hU h0 ⟨ψ, hψ⟩
  convert h using 1
  funext x
  rw [cutL_apply]
  simp only [PositivityTheory.PfBern.cocyclesToWachVectorsExponent.cutFun]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem det_cj {n : ℕ} (p x : GL (Fin (n + 1)) k) :
    ((p * x * p⁻¹ : GL (Fin (n + 1)) k).val).det = (x.val).det := by
  simp only [Units.val_mul, Matrix.det_mul]
  rw [mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one, one_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem cutL_cj {n : ℕ} (U : Set k) (p : GL (Fin (n + 1)) k) (ψ : Mx k n → ℂ) :
    cutL U (ψ ∘ cj p) = fun x => cutL U ψ (p * x * p⁻¹) := by
  funext x
  rw [cutL_apply, cutL_apply, det_cj]
  rfl

end PositivityTheory.RgUd.AB.Pf

namespace PositivityTheory.RgUd.AB.Pf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem thmA_of_core : CoreX k → ThmT k → ThmA k := by
  intro hC hT n Λ hP p f hf
  classical
  have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf.1
  let φ : SB (GL (Fin (n + 1)) k) := ⟨f, hf'⟩
  let ψ : SB (Mx k n) := ⟨PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ φ, PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ_mem φ⟩
  have hdet : Continuous fun x : GL (Fin (n + 1)) k => (x.val).det :=
    (continuous_id.matrix_det).comp Units.continuous_val
  obtain ⟨U, hU, hCU, h0⟩ := PositivityTheory.PfBern.cocyclesToWachVectorsExponent.exists_clopen_local
    ((fun x : GL (Fin (n + 1)) k => (x.val).det) '' tsupport f)
    (hf'.2.isCompact.image hdet)
    (by
      rintro ⟨x, -, hx⟩
      exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero hx)
  have hfeq : cutL U ψ.1 = f := by
    funext x
    rw [cutL_apply]
    split_ifs with h
    · exact PositivityTheory.PfBern.cocyclesToWachVectorsExponent.extZ_val φ x
    · symm
      by_contra hne
      exact h (hCU ⟨x, subset_tsupport _ hne, rfl⟩)
  let Λ' : (Mx k n → ℂ) →ₗ[ℂ] ℂ := Λ ∘ₗ cutL U
  have hPX : PInvX Λ' := by
    intro q hq g hg
    show Λ (cutL U (g ∘ cj q)) = Λ (cutL U g)
    rw [cutL_cj]
    exact hP q hq _ ((mem_SB_iff_supportedIn _).mp (cutL_mem U hU h0 hg))
  have hGX := hC hT n Λ' hPX p ψ.1 ψ.2
  have e1 : (fun g => f (p * g * p⁻¹)) = cutL U (ψ.1 ∘ cj p) := by
    rw [cutL_cj, hfeq]
  have e2 : Λ (cutL U (ψ.1 ∘ cj p)) = Λ (cutL U ψ.1) := hGX
  rw [e1, e2, hfeq]

end PositivityTheory.RgUd.AB.Pf
