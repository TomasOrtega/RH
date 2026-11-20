import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

/- English proof (translation)
Take `⟨s, hs⟩` from `hM`. Establish `hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M` using `fun t ht x hx => by`. Establish `h : t.val *ᵥ x ∈ act t M` using `mem_act.2 ⟨x, hx, rfl⟩`. Rewrite `h` using `[ht]`. Then use the resulting hypothesis. Establish `hsM : ∀ x : s, x.1 ∈ M` using `fun x => hs ▸ Submodule.subset_span x.2`.

Establish `hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M`. Introduce `t x`. Take `⟨r, hr, -⟩` from `hS.2 _ (hmem t.1 t.2 x.1 (hsM x))`. Conclude with `⟨⟨r, hr.1⟩, hr.2⟩`. Use `choose f hf using hex`.

Establish `hsec : ∀ y : Set.range f, ∃ t, f t = y.1` using `fun y => y.2`. Use `choose g hg using hsec`. Establish `: Fintype (Set.range f)` using `Fintype.ofFinite _`. Use `⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `(g y).2`. Use `set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀`. Establish `hft : f t₀ = f ⟨t, ht⟩` using `hg _`. Establish `hinv : act (t₀.1)⁻¹ M = M`.

Establish `h` using `act_mul (t₀.1)⁻¹ t₀.1 M`. Rewrite `h` using `[inv_mul_cancel, act_one, t₀.2]`. Conclude with `h.symm`. Use `⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[act_mul, ht, hinv]`.

Introduce `v hv`. Rewrite `hv` using `[← hs]`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Establish `h1` using `hf ⟨t, ht⟩ ⟨x, hx⟩`.

Establish `h2` using `hf t₀ ⟨x, hx⟩`. Rewrite `h2` using `[hft]`. Establish `h3` using `sub_mem h1 h2`. Rewrite `h3` using `[sub_sub_sub_cancel_right]`. Take `⟨w, hw, hw'⟩` from `mem_smul_iff.1 h3`.

Use `mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ a hx`. Rewrite using `[mul_inv_cancel_left]`.
-/
theorem stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hmem : ∀ t : GL ι k, act t M = M → ∀ x ∈ M, t.val *ᵥ x ∈ M := fun t ht x hx => by
    have h : t.val *ᵥ x ∈ act t M := mem_act.2 ⟨x, hx, rfl⟩
    rwa [ht] at h
  have hsM : ∀ x : s, x.1 ∈ M := fun x => hs ▸ Submodule.subset_span x.2
  have hex : ∀ (t : {t : GL ι k // act t M = M}) (x : s), ∃ r : S, t.1.val *ᵥ x.1 - r.1 ∈ ϖ • M := by
    intro t x
    obtain ⟨r, hr, -⟩ := hS.2 _ (hmem t.1 t.2 x.1 (hsM x))
    exact ⟨⟨r, hr.1⟩, hr.2⟩
  choose f hf using hex
  have hsec : ∀ y : Set.range f, ∃ t, f t = y.1 := fun y => y.2
  choose g hg using hsec
  have : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y => (g y).1, ?_, fun t ht => ?_⟩
  · intro t ht
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    exact (g y).2
  · set t₀ := g ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩ with ht₀
    have hft : f t₀ = f ⟨t, ht⟩ := hg _
    have hinv : act (t₀.1)⁻¹ M = M := by
      have h := act_mul (t₀.1)⁻¹ t₀.1 M
      rw [inv_mul_cancel, act_one, t₀.2] at h
      exact h.symm
    refine ⟨t₀.1, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (t₀.1)⁻¹ * t, ?_, ?_, ?_⟩
    · rw [act_mul, ht, hinv]
    · intro v hv
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        have h1 := hf ⟨t, ht⟩ ⟨x, hx⟩
        have h2 := hf t₀ ⟨x, hx⟩
        rw [hft] at h2
        have h3 := sub_mem h1 h2
        rw [sub_sub_sub_cancel_right] at h3
        obtain ⟨w, hw, hw'⟩ := mem_smul_iff.1 h3
        refine mem_smul_iff.2 ⟨_, hmem _ hinv w hw, ?_⟩
        rw [← Matrix.mulVec_smul, hw', Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Units.inv_mul, Units.val_mul]
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    · rw [mul_inv_cancel_left]

end GlobalTheory.RootEx.UnfoldShape
