import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.KirFin

/- English proof (translation)
Introduce `F _ ψ hψ hψ1 ι _ K hK Φ hΦ`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hψ1 (AddChar.ext _ _ h)`.

Set `χ : (ι → F) → (ι → F) → ℂ` to `fun v r => ψ (r ⬝ᵥ v)`. Set `S : Set ((ι → F) → ℂ)` to `Set.range χ`. Establish `hχmul : ∀ v w, χ v * χ w = χ (v + w)`. Introduce `v w`. Use function extensionality and compare the values at `r`.

Simplify using `[χ, dotProduct_add, AddChar.map_add_eq_mul]`. Establish `hχ0 : χ 0 = 1` using `by funext r; simp [χ]`. Establish `hlc : ∀ v, IsLocallyConstant (χ v)` using `fun v => hψ.comp_continuous (continuous_id.dotProduct continuous_const)`. Set `L : Subalgebra ℂ ((ι → F) → ℂ)` to `{ carrier := {a | IsLocallyConstant a} mul_mem' := fun ha hb => IsLocallyConstant.mul ha hb add_mem' := fun ha hb => IsLocallyConstant.add ha hb algebraMap_mem' := fun c => IsLocallyConstant.const _ }`. Set `A` to `Algebra.adjoin ℂ S`.

Establish `hAL : A ≤ L` using `Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hlc v)`. Establish `hAspan : ∀ a ∈ A, a ∈ Submodule.span ℂ S`. Introduce `a ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`.

Consider the case `algebraMap c`. Establish `: algebraMap ℂ ((ι → F) → ℂ) c = c • χ 0`. Rewrite using `[hχ0, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)`.

Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy`. Use `Submodule.mul_mem_mul hx hy` as an intermediate fact. Rewrite `this` using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_ this` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨v + w, (hχmul v w).symm⟩`. Set `ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ)` to `{ toFun := fun a x => a x.1 map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl commutes' := fun _ => rfl }`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Take `⟨a, ha, e⟩` from `mem_of_separates (A.map ρ) (by rintro _ ⟨a, ha, rfl⟩; exact (hAL ha).comp_continuous continuous_subtype_val) (by`.

Introduce `x y hxy`. Take `⟨i, hi⟩` from `Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)`. Use `⟨ρ (χ (Pi.single i (t / (x.1 i - y.1 i)))), ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, fun h => ht ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h`. Rewrite `h` using `[dotProduct_single, dotProduct_single]`.

Establish `h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i))`. Use `sub_ne_zero.2 hi` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h2, AddChar.map_add_eq_mul]`.

Conclude with `(mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)`. Use the proof step `(hΦ.comp_continuous continuous_subtype_val)`. Take `⟨T, hT⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 (hAspan a ha)`. Use `⟨T, fun r hr => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun e ⟨r, hr⟩`.

Express the relevant statement in the definitionally equal form `a r = Φ r at h1`. Rewrite using `[← h1, ← hT]`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, χ]`.
-/
theorem exists_charSum_eq_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 →
    ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ →
    ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  intro F _ ψ hψ hψ1 ι _ K hK Φ hΦ
  classical
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (AddChar.ext _ _ h)
  let χ : (ι → F) → (ι → F) → ℂ := fun v r => ψ (r ⬝ᵥ v)
  let S : Set ((ι → F) → ℂ) := Set.range χ
  have hχmul : ∀ v w, χ v * χ w = χ (v + w) := by
    intro v w; funext r; simp [χ, dotProduct_add, AddChar.map_add_eq_mul]
  have hχ0 : χ 0 = 1 := by funext r; simp [χ]
  have hlc : ∀ v, IsLocallyConstant (χ v) := fun v =>
    hψ.comp_continuous (continuous_id.dotProduct continuous_const)
  let L : Subalgebra ℂ ((ι → F) → ℂ) :=
    { carrier := {a | IsLocallyConstant a}
      mul_mem' := fun ha hb => IsLocallyConstant.mul ha hb
      add_mem' := fun ha hb => IsLocallyConstant.add ha hb
      algebraMap_mem' := fun c => IsLocallyConstant.const _ }
  let A := Algebra.adjoin ℂ S
  have hAL : A ≤ L := Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hlc v)
  have hAspan : ∀ a ∈ A, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap c =>
      have : algebraMap ℂ ((ι → F) → ℂ) c = c • χ 0 := by
        rw [hχ0, Algebra.algebraMap_eq_smul_one]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨v + w, (hχmul v w).symm⟩
  let ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ) :=
    { toFun := fun a x => a x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨a, ha, e⟩ := mem_of_separates (A.map ρ)
    (by rintro _ ⟨a, ha, rfl⟩; exact (hAL ha).comp_continuous continuous_subtype_val)
    (by
      intro x y hxy
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)
      refine ⟨ρ (χ (Pi.single i (t / (x.1 i - y.1 i)))), ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩,
        fun h => ht ?_⟩
      change ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h
      rw [dotProduct_single, dotProduct_single] at h
      have h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i)) := by
        have := sub_ne_zero.2 hi
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul] at h
      exact (mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)
    (hΦ.comp_continuous continuous_subtype_val)
  obtain ⟨T, hT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hAspan a ha)
  refine ⟨T, fun r hr => ?_⟩
  have h1 := congrFun e ⟨r, hr⟩
  change a r = Φ r at h1
  rw [← h1, ← hT]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, χ]

end GlobalTheory.JSW.KirFin
