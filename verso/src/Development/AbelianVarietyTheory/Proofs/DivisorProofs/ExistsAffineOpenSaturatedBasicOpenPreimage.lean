import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

/- English proof (translation)
Introduce `B' C Y i q hi hq hB y O hO hyO`. Establish `hF : (q ⁻¹' {q y}).Finite` using `q.finite_preimage_singleton (q y)`. Take `⟨V₀, hV₀, hFV₀⟩` from `hB ((hF.image i).toFinset)`. Establish `hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀)` using `hV₀.preimage i`. Take `⟨h, hFh, hhO⟩` from `GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hx`. Simplify using `[hx, hyO])`. Establish `hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ)` using `q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl`. Establish `hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ`. Introduce and unpack `⟨x, hx, hxy⟩`.

Conclude with `hx (hFh (by simpa using hxy))`. Set `W : C.Opens` to `⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩`. Take `⟨r, hrW, hyr⟩` from `hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO`. Establish `hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h`. Introduce `x hx`.

Assume the negation of the conclusion as `hxh`. Conclude with `hrW hx ⟨x, hxh, rfl⟩`. Establish `hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r)` using `Scheme.preimage_basicOpen q r`. Take `⟨f', hf'⟩` from `hY₀.basicOpen_basicOpen_is_basicOpen h (Y.presheaf.map (homOfLE hhO).op (q.app O r))`. Rewrite `hf'` using `[Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle]`.

Take `⟨t, ht⟩` from `i.app_surjective V₀ hV₀ f'`. Use `⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩` and prove the remaining obligations. Establish `: y ∈ i ⁻¹ᵁ B'.basicOpen t`. Rewrite using `[Scheme.preimage_basicOpen, ht, hf']`. Conclude with `hyr`.

Conclude with `this`. Rewrite using `[Scheme.preimage_basicOpen, ht, hf']`.
-/
theorem exists_affine_basicOpen_nbhd : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i →
    IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O →
    ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  intro B' C Y i q hi hq hB y O hO hyO
  have hF : (q ⁻¹' {q y}).Finite := q.finite_preimage_singleton (q y)
  classical
  obtain ⟨V₀, hV₀, hFV₀⟩ := hB ((hF.image i).toFinset)
  have hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀) := hV₀.preimage i
  obtain ⟨h, hFh, hhO⟩ := GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF
    (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx; simp [hx, hyO])
  have hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ) :=
    q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl
  have hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hFh (by simpa using hxy))
  let W : C.Opens := ⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩
  obtain ⟨r, hrW, hyr⟩ := hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO
  have hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h := by
    intro x hx
    by_contra hxh
    exact hrW hx ⟨x, hxh, rfl⟩
  have hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r) := Scheme.preimage_basicOpen q r
  obtain ⟨f', hf'⟩ := hY₀.basicOpen_basicOpen_is_basicOpen h
    (Y.presheaf.map (homOfLE hhO).op (q.app O r))
  rw [Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle] at hf'
  obtain ⟨t, ht⟩ := i.app_surjective V₀ hV₀ f'
  refine ⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩
  · have : y ∈ i ⁻¹ᵁ B'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, hf']; exact hyr
    exact this
  · rw [Scheme.preimage_basicOpen, ht, hf']

end GlobalTheory.Pinch
