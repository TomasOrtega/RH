import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxComplexPadicCoboundaryAlgebraicIntegerStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Unfold `IK at hσ`. Proceed by induction on `hσ using Subgroup.closure_induction with`. Consider the case `mem σ h => exact h`. Consider the case `one => intro x _`. Simplify using the standard rewrite rules.

Consider the case `mul σ τ _ _ hσ hτ`. Introduce `x hx`. Establish `h1 : ‖(τ : GQ l) x‖ ≤ 1` using `by rw [GlobalTheory.RingBasics.norm_gal]; exact hx`. Establish `e : ((σ * τ : ↥(GK K)) : GQ l) x - x = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x)`. Rewrite using `[Subgroup.coe_mul, AlgEquiv.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))`. Consider the case `inv σ _ hσ`. Introduce `x hx`.

Establish `h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1` using `by rw [GlobalTheory.RingBasics.norm_gal]; exact hx`. Establish `h2` using `hσ _ h1`. Rewrite `h2` using `[← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev]`. Rewrite using `[Subgroup.coe_inv]`. Conclude with `h2`.
-/
theorem norm_sub_lt_one_of_mem_inertia {l : ℕ} [Fact l.Prime] (K : FinExt l) (σ : ↥(GK K)) (hσ : σ ∈ IK K) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  unfold IK at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ h => exact h
  | one => intro x _; simp
  | mul σ τ _ _ hσ hτ =>
    intro x hx
    have h1 : ‖(τ : GQ l) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have e : ((σ * τ : ↥(GK K)) : GQ l) x - x
        = ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
      rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hσ _ h1) (hτ _ hx))
  | inv σ _ hσ =>
    intro x hx
    have h1 : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rw [GlobalTheory.RingBasics.norm_gal]; exact hx
    have h2 := hσ _ h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, norm_sub_rev] at h2
    rw [Subgroup.coe_inv]
    exact h2

/- English proof (translation)
Introduce `l _ K N hanti hopen hpow hroot hchar`. Establish `: FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l))` using `K.2`. Establish `hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l))` using `IntermediateField.fixingSubgroup_isOpen _`. Establish `hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k` using `fun k σ => Subgroup.mem_map_iff_mem (GK K).subtype_injective`. Take `⟨k, hk⟩` from `GlobalTheory.T.noDetectedSubgroupTowerRat_proof l (fun k => (N k).map (GK K).subtype) (fun i j hij => Subgroup.map_mono (hanti hij)) (fun k => hGK.isOpenMap_subtype_val _ (hopen k)) (by`.

Introduce and unpack `k _ ⟨σ, hσ, rfl⟩`. Conclude with `⟨σ ^ l, hpow k σ hσ, rfl⟩)`. Use the proof step `(by`. Introduce and unpack `j _ ⟨σ, hσ, rfl⟩ h`. Conclude with `⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)`.

Use the proof step `(by`. Introduce `r`. Take `⟨k₀, hk₀⟩` from `hchar r`. Use `⟨k₀, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨ι, hι, x, a, h1, h2⟩` from `hk₀ k hk`.

Establish `key` using `fun i => GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i) (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by`. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Use `h1 i σ hσ` as an intermediate fact. Simplify using `using this)`. Use `choose y b hy hb using key`.

Use `⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨σ, hσ, rfl⟩ h`. Use `⟨σ, h2 σ hσ fun i => ?_, rfl⟩` and prove the remaining obligations. Use `hb i _ (h i)` as an intermediate fact. Simplify using `using this)`.

Use `⟨k, fun j σ hσ => ?_⟩` and prove the remaining obligations. Conclude with `(hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))`.
-/
theorem noTower : NoTower := by
  classical
  intro l _ K N hanti hopen hpow hroot hchar
  have : FiniteDimensional ℚ_[l] (K : IntermediateField ℚ_[l] (Om l)) := K.2
  have hGK : IsOpen ((GK K : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen _
  have hmem : ∀ k (σ : ↥(GK K)), (σ : GQ l) ∈ (N k).map (GK K).subtype ↔ σ ∈ N k := fun k σ =>
    Subgroup.mem_map_iff_mem (GK K).subtype_injective
  obtain ⟨k, hk⟩ := GlobalTheory.T.noDetectedSubgroupTowerRat_proof l (fun k => (N k).map (GK K).subtype)
    (fun i j hij => Subgroup.map_mono (hanti hij))
    (fun k => hGK.isOpenMap_subtype_val _ (hopen k))
    (by
      rintro k _ ⟨σ, hσ, rfl⟩
      exact ⟨σ ^ l, hpow k σ hσ, rfl⟩)
    (by
      rintro j _ ⟨σ, hσ, rfl⟩ h
      exact ⟨σ, hroot j σ hσ ((hmem _ (σ ^ l)).1 h), rfl⟩)
    (by
      intro r
      obtain ⟨k₀, hk₀⟩ := hchar r
      refine ⟨k₀, fun k hk => ?_⟩
      obtain ⟨ι, hι, x, a, h1, h2⟩ := hk₀ k hk
      have key := fun i => GlobalTheory.T.approx_complexPadic_coboundary_algebraic_integer l r ((N k).map (GK K).subtype : Subgroup (GQ l)) (x i)
        (fun σ => if h : σ ∈ GK K then a i ⟨σ, h⟩ else 0) (by
          rintro _ ⟨σ, hσ, rfl⟩
          have := h1 i σ hσ
          simpa using this)
      choose y b hy hb using key
      refine ⟨ι, hι, y, b, fun i σ hσ => hy i σ hσ, ?_⟩
      rintro _ ⟨σ, hσ, rfl⟩ h
      refine ⟨σ, h2 σ hσ fun i => ?_, rfl⟩
      have := hb i _ (h i)
      simpa using this)
  refine ⟨k, fun j σ hσ => ?_⟩
  exact (hmem j σ).1 (hk j _ ((hmem k σ).2 hσ.2) (norm_sub_lt_one_of_mem_inertia K σ hσ.1))

end GlobalTheory.PMon.Ram
