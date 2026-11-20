import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwTrUnit

/- English proof (translation)
Distinguish the cases in `hW : Module.Finite ℂ W`. Use `haveI : Subsingleton W := Module.finrank_zero_iff.1 h`. Rewrite using `[show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]`. Unfold `LinearMap.trace`. Rewrite using `[dif_neg]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨s, ⟨b⟩⟩`. Conclude with `hW (Module.Finite.of_basis b)`.
-/
theorem trace_eq_zero_of_finrank_eq_zero (W : Type) [AddCommGroup W] [Module ℂ W] (h : Module.finrank ℂ W = 0)
    (L : W →ₗ[ℂ] W) : LinearMap.trace ℂ W L = 0 := by
  by_cases hW : Module.Finite ℂ W
  · haveI : Subsingleton W := Module.finrank_zero_iff.1 h
    rw [show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · unfold LinearMap.trace
    rw [dif_neg]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

/- English proof (translation)
Establish `hcl : IsClosed (K' : Set G)` using `K'.isClosed_of_isOpen ho`. Establish `hc : IsCompact (K' : Set G)` using `hK.of_isClosed_subset hcl hle`. Use `⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `: k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G)` using `K'.mul_mem_cancel_left hk`. Simplify using `only [Set.indicator_apply, this, Pi.one_apply]`.

Establish `: x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G)` using `K'.mul_mem_cancel_right hk`. Simplify using `only [Set.indicator_apply, this, Pi.one_apply]`.
-/
theorem isHecke_indicator {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) :
    IsHecke K' ((K' : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K' : Set G) := K'.isClosed_of_isOpen ho
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset hcl hle
  refine ⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · have : k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_left hk
    simp only [Set.indicator_apply, this, Pi.one_apply]
  · have : x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_right hk
    simp only [Set.indicator_apply, this, Pi.one_apply]

/- English proof (translation)
Take `⟨x₀, hx₀, hL⟩` from `GlobalTheory.TwTrLin.levOp_unit ρ K K'`. Establish `hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v` using `fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀`. Establish `hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K'`. Introduce `v hv`. Rewrite using `[hL, LinearMap.smul_apply, hfx v hv]`.

Conclude with `Submodule.smul_mem _ _ hv`. Rewrite using `[GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]`. Establish `hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id`. Use extensionality with `x`. Simplify using `[LinearMap.restrict_apply, hL, hfx x.1 x.2]`.

Rewrite using `[hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]`.
-/
theorem twTr_indicator {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) : twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) := by
  obtain ⟨x₀, hx₀, hL⟩ := GlobalTheory.TwTrLin.levOp_unit ρ K K'
  have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀
  have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [hL, LinearMap.smul_apply, hfx v hv]
    exact Submodule.smul_mem _ _ hv
  rw [GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]
  have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext x
    simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
  rw [hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]

/- English proof (translation)
Introduce `E _ _ _ n w K' hlev σ`. Establish `hKc` using `GlobalTheory.LocFinU.isCompact_KL n w`. Use `⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1, twTr_indicator _ _ _, fun h g => ?_⟩` and prove the remaining obligations. Unfold `twTr`. Use `split_ifs with hm`.

Conclude with `trace_eq_zero_of_finrank_eq_zero _ h _`. Both sides reduce to the same expression.
-/
theorem twTr_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  intro E _ _ _ n w K' hlev σ
  have hKc := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1,
    twTr_indicator _ _ _, fun h g => ?_⟩
  unfold twTr
  split_ifs with hm
  · exact trace_eq_zero_of_finrank_eq_zero _ h _
  · rfl

end GlobalTheory.TwTrUnit
