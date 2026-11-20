import Mathlib

noncomputable section

open TensorProduct

namespace PositivityTheory.KB.NaturalTheta

section

variable {C2 C1 C0 H V2 V1 V0 : Type} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
  [AddCommGroup H] [Module ℤ H]
  [AddCommGroup V2] [AddCommGroup V1] [AddCommGroup V0]
  [Module ℝ V2] [Module ℝ V1] [Module ℝ V0]
  (d1 : C2 →ₗ[ℤ] C1) (d0 : C1 →ₗ[ℤ] C0) (p : LinearMap.ker d0 →ₗ[ℤ] H)
  (e2 : ℝ ⊗[ℤ] C2 ≃ₗ[ℝ] V2) (e1 : ℝ ⊗[ℤ] C1 ≃ₗ[ℝ] V1) (e0 : ℝ ⊗[ℤ] C0 ≃ₗ[ℝ] V0)
  (D1 : V2 →ₗ[ℝ] V1) (D0 : V1 →ₗ[ℝ] V0)

def jz : ℝ ⊗[ℤ] LinearMap.ker d0 →ₗ[ℝ] V1 :=
  e1.toLinearMap ∘ₗ (LinearMap.ker d0).subtype.baseChange ℝ

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem jz_injective : Function.Injective (jz d0 e1) := by
  unfold jz
  rw [LinearMap.coe_comp]
  refine e1.injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem range_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    LinearMap.range (jz d0 e1) = LinearMap.ker D0 := by
  have hex := Module.Flat.lTensor_exact ℝ (LinearMap.exact_subtype_ker_map d0)
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    have h1 := congrArg (fun f => f (((LinearMap.ker d0).subtype.baseChange ℝ) w)) h0
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor,
      hex.apply_apply_eq_zero w, map_zero]
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y, rfl⟩ := e1.surjective x
    have h1 := congrArg (fun f => f y) h0
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [h1] at hx
    have hy : (d0.baseChange ℝ) y = 0 := by
      rw [← map_zero e0] at hx
      exact e0.injective hx
    rw [LinearMap.baseChange_eq_ltensor] at hy
    obtain ⟨w, hw⟩ := (hex y).mp hy
    refine ⟨w, ?_⟩
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.baseChange_eq_ltensor, hw]

def th (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    LinearMap.ker D0 →ₗ[ℝ] ℝ ⊗[ℤ] H :=
  p.baseChange ℝ ∘ₗ (LinearEquiv.ofInjective _ (jz_injective d0 e1)).symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ (range_jz d0 e1 e0 D0 h0).symm).toLinearMap

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem th_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (w : ℝ ⊗[ℤ] LinearMap.ker d0) (hw : jz d0 e1 w ∈ LinearMap.ker D0) :
    th d0 p e1 e0 D0 h0 ⟨jz d0 e1 w, hw⟩ = p.baseChange ℝ w := by
  simp only [th, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (z : LinearMap.ker D0) : ∃ w, jz d0 e1 w = z.1 := by
  have hz : z.1 ∈ LinearMap.range (jz d0 e1) := by
    rw [range_jz d0 e1 e0 D0 h0]
    exact z.2
  exact LinearMap.mem_range.mp hz

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem th_surjective (hp : Function.Surjective p)
    (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    Function.Surjective (th d0 p e1 e0 D0 h0) := by
  intro y
  have hs : Function.Surjective (p.baseChange ℝ) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ hp
  obtain ⟨w, rfl⟩ := hs y
  have hw : jz d0 e1 w ∈ LinearMap.ker D0 := by
    rw [← range_jz d0 e1 e0 D0 h0]
    exact LinearMap.mem_range_self _ w
  exact ⟨⟨jz d0 e1 w, hw⟩, th_jz d0 p e1 e0 D0 h0 w hw⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem th_eq_zero_iff (hdd : d0 ∘ₗ d1 = 0) (hker : ∀ x, p x = 0 ↔ x.1 ∈ LinearMap.range d1)
    (hp : Function.Surjective p)
    (h1 : D1 ∘ₗ e2.toLinearMap = e1.toLinearMap ∘ₗ d1.baseChange ℝ)
    (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) (z : LinearMap.ker D0) :
    th d0 p e1 e0 D0 h0 z = 0 ↔ z.1 ∈ LinearMap.range D1 := by
  obtain ⟨zv, hzv⟩ := z
  obtain ⟨w, hw⟩ := exists_jz d0 e1 e0 D0 h0 ⟨zv, hzv⟩
  simp only at hw
  subst hw
  rw [th_jz d0 p e1 e0 D0 h0 w hzv]
  have hmem : ∀ c, d1 c ∈ LinearMap.ker d0 := fun c => by
    rw [LinearMap.mem_ker]
    simpa using LinearMap.congr_fun hdd c
  obtain ⟨g, hg⟩ : ∃ g : C2 →ₗ[ℤ] LinearMap.ker d0, (LinearMap.ker d0).subtype ∘ₗ g = d1 :=
    ⟨d1.codRestrict _ hmem, LinearMap.subtype_comp_codRestrict _ _ _⟩
  have hgx : ∀ c, ((g c : LinearMap.ker d0) : C1) = d1 c := fun c => LinearMap.congr_fun hg c
  have hexZ : Function.Exact g p := by
    intro x
    rw [hker x]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, Subtype.ext ((hgx c).trans hc)⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (hgx c).symm⟩
  have hexR := lTensor_exact ℝ hexZ hp
  have key : ∀ u, jz d0 e1 (g.baseChange ℝ u) = D1 (e2 u) := by
    intro u
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← LinearMap.comp_apply ((LinearMap.ker d0).subtype.baseChange ℝ),
      ← LinearMap.baseChange_comp, hg]
    have := LinearMap.congr_fun h1 u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    exact this.symm
  rw [LinearMap.baseChange_eq_ltensor, hexR w]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨e2 u, ?_⟩
    rw [← key u, LinearMap.baseChange_eq_ltensor]
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := e2.surjective v
    refine ⟨u, ?_⟩
    apply jz_injective d0 e1
    rw [← LinearMap.baseChange_eq_ltensor, key u, hv]

end

section Nat

variable {C1 C0 H V1 V0 C1' C0' H' V1' V0' : Type} [AddCommGroup C1] [AddCommGroup C0]
  [AddCommGroup H] [AddCommGroup V1] [AddCommGroup V0] [Module ℝ V1] [Module ℝ V0]
  [AddCommGroup C1'] [AddCommGroup C0'] [AddCommGroup H'] [AddCommGroup V1'] [AddCommGroup V0']
  [Module ℤ H] [Module ℤ H']
  [Module ℝ V1'] [Module ℝ V0']
  (d0 : C1 →ₗ[ℤ] C0) (p : LinearMap.ker d0 →ₗ[ℤ] H)
  (e1 : ℝ ⊗[ℤ] C1 ≃ₗ[ℝ] V1) (e0 : ℝ ⊗[ℤ] C0 ≃ₗ[ℝ] V0) (D0 : V1 →ₗ[ℝ] V0)
  (d0' : C1' →ₗ[ℤ] C0') (p' : LinearMap.ker d0' →ₗ[ℤ] H')
  (e1' : ℝ ⊗[ℤ] C1' ≃ₗ[ℝ] V1') (e0' : ℝ ⊗[ℤ] C0' ≃ₗ[ℝ] V0') (D0' : V1' →ₗ[ℝ] V0')

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem th_natural (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (h0' : D0' ∘ₗ e1'.toLinearMap = e0'.toLinearMap ∘ₗ d0'.baseChange ℝ)
    (c1 : C1 →ₗ[ℤ] C1') (q : H →ₗ[ℤ] H') (F : V1 →ₗ[ℝ] V1')
    (hF : F ∘ₗ e1.toLinearMap = e1'.toLinearMap ∘ₗ c1.baseChange ℝ)
    (hc : ∀ x ∈ LinearMap.ker d0, c1 x ∈ LinearMap.ker d0')
    (hq : ∀ x : LinearMap.ker d0, p' ⟨c1 x, hc x x.2⟩ = q (p x))
    (z : LinearMap.ker D0) (z' : LinearMap.ker D0') (hz : z'.1 = F z.1) :
    th d0' p' e1' e0' D0' h0' z' = q.baseChange ℝ (th d0 p e1 e0 D0 h0 z) := by
  obtain ⟨zv, hzv⟩ := z
  obtain ⟨w, hw⟩ := exists_jz d0 e1 e0 D0 h0 ⟨zv, hzv⟩
  simp only at hw
  subst hw
  obtain ⟨zv', hzv'⟩ := z'
  simp only at hz
  subst hz
  rw [th_jz d0 p e1 e0 D0 h0 w hzv]
  have hcomp : c1 ∘ₗ (LinearMap.ker d0).subtype
      = (LinearMap.ker d0').subtype ∘ₗ c1.restrict hc := LinearMap.ext fun x => rfl
  have hj : F (jz d0 e1 w) = jz d0' e1' ((c1.restrict hc).baseChange ℝ w) := by
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have := LinearMap.congr_fun hF ((LinearMap.ker d0).subtype.baseChange ℝ w)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, ← LinearMap.comp_apply (c1.baseChange ℝ), ← LinearMap.baseChange_comp, hcomp,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hmem : jz d0' e1' ((c1.restrict hc).baseChange ℝ w) ∈ LinearMap.ker D0' := hj ▸ hzv'
  have heq : (⟨F (jz d0 e1 w), hzv'⟩ : LinearMap.ker D0')
      = ⟨jz d0' e1' ((c1.restrict hc).baseChange ℝ w), hmem⟩ := Subtype.ext hj
  rw [heq, th_jz d0' p' e1' e0' D0' h0' _ hmem, ← LinearMap.comp_apply (p'.baseChange ℝ),
    ← LinearMap.baseChange_comp, ← LinearMap.comp_apply (q.baseChange ℝ),
    ← LinearMap.baseChange_comp]
  rw [show p' ∘ₗ c1.restrict hc = q ∘ₗ p from LinearMap.ext fun x => hq x]

end Nat

end PositivityTheory.KB.NaturalTheta
