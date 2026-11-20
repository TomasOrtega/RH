import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs`. Establish `hg : IsFinite (spMap (algebraMap R R₁))`. Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.2 inferInstance`. Establish `hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁))`.

Rewrite using `[flat_and_surjective_SpecMap_iff]`. Conclude with `RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance`. Establish `: Flat (spMap (algebraMap R R₁))` using `hff.1`. Establish `: Surjective (spMap (algebraMap R R₁))` using `hff.2`. Establish `: IsFinite b` using `MorphismProperty.of_isPullback H.flip hg`.

Establish `: QuasiSeparatedSpace X` using `quasiSeparatedSpace_of_quasiSeparated p`. Set `O' : X.Opens` to `⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩`. Establish `hsO' : ∀ x ∈ s, x ∈ O'`. Introduce and unpack `x hx ⟨z, hz, rfl⟩`. Conclude with `hz (hs z hx)`.

Establish `key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O'`. Introduce `x hx`. Take `⟨U, hU, hxU, hUO⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)`. Conclude with `⟨U, hU, hxU, hUO⟩`. Use `choose U hU hxU hUO using key`.

Set `V : X.Opens` to `⨆ x : s, U x.1 x.2`. Establish `hVO : V ≤ O'` using `iSup_le fun x => hUO x.1 x.2`. Establish `hsV : ∀ x ∈ s, x ∈ V` using `fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩`. Establish `hVc : IsCompact (V : Set X)`. Rewrite using `[TopologicalSpace.Opens.coe_iSup]`.

Conclude with `isCompact_iUnion fun x => (hU x.1 x.2).isCompact`. Establish `hVq : IsQuasiSeparated (V : Set X)` using `IsQuasiSeparated.of_quasiSeparatedSpace _`. Establish `hVW : b ⁻¹ᵁ V ≤ W`. Introduce `z hz`. Assume the negation of the conclusion as `h`.

Conclude with `hVO hz ⟨z, h, rfl⟩`. Establish `hfin : (b ⁻¹' (s : Set X)).Finite` using `s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x`. Take `⟨f, hfV, hft⟩` from `GlobalTheory.T.exists_basicOpen_between_finset_and_open' X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))`. Set `f' : Γ(X₁, b ⁻¹ᵁ V)` to `X₁.presheaf.map (homOfLE hVW).op f`. Establish `hf' : X₁.basicOpen f' = X₁.basicOpen f`.

Rewrite using `[Scheme.basicOpen_res]`. Conclude with `inf_eq_right.2 hfV`. Take `⟨n, hn⟩` from `GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange R R₁ X X₁ p p₁ b H V hVc hVq f'`. Use `⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩` and prove the remaining obligations. Use `swap`.

Rewrite using `[hf']`. Conclude with `hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))`. Establish `hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f`. Introduce `z hz`. Rewrite using `[← hf']`.

Conclude with `((hn (b z)).1 hz).2 z rfl`. Establish `hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n)`. Set `g : Γ(X₁, X₁.basicOpen f)` to `X₁.presheaf.map (homOfLE hfV).op (b.app V n)`. Establish `e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n`. Rewrite using `[Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]`.

Conclude with `inf_eq_right.2 hle`. Rewrite using `[← e]`. Conclude with `(hW.basicOpen f).basicOpen g`. Establish `: IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme` using `hA`. Conclude with `isAffine_of_isPullback_of_flat_surjective ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)`.
-/
theorem exists_isAffineOpen_of_preimage_le_affine : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0})
    (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) →
    IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X,
    (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs
  classical

  have hg : IsFinite (spMap (algebraMap R R₁)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁)) := by
    rw [flat_and_surjective_SpecMap_iff]
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (spMap (algebraMap R R₁)) := hff.1
  have : Surjective (spMap (algebraMap R R₁)) := hff.2
  have : IsFinite b := MorphismProperty.of_isPullback H.flip hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p

  let O' : X.Opens := ⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsO' : ∀ x ∈ s, x ∈ O' := by
    rintro x hx ⟨z, hz, rfl⟩
    exact hz (hs z hx)
  have key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O' := by
    intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)
    exact ⟨U, hU, hxU, hUO⟩
  choose U hU hxU hUO using key
  let V : X.Opens := ⨆ x : s, U x.1 x.2
  have hVO : V ≤ O' := iSup_le fun x => hUO x.1 x.2
  have hsV : ∀ x ∈ s, x ∈ V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩
  have hVc : IsCompact (V : Set X) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hU x.1 x.2).isCompact
  have hVq : IsQuasiSeparated (V : Set X) := IsQuasiSeparated.of_quasiSeparatedSpace _
  have hVW : b ⁻¹ᵁ V ≤ W := by
    intro z hz
    by_contra h
    exact hVO hz ⟨z, h, rfl⟩

  have hfin : (b ⁻¹' (s : Set X)).Finite :=
    s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x
  obtain ⟨f, hfV, hft⟩ := GlobalTheory.T.exists_basicOpen_between_finset_and_open' X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset
    (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))
  let f' : Γ(X₁, b ⁻¹ᵁ V) := X₁.presheaf.map (homOfLE hVW).op f
  have hf' : X₁.basicOpen f' = X₁.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfV
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange R R₁ X X₁ p p₁ b H V hVc hVq f'
  refine ⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩
  swap
  · rw [hf']
    exact hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))

  have hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f := by
    intro z hz
    rw [← hf']
    exact ((hn (b z)).1 hz).2 z rfl
  have hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n) := by
    let g : Γ(X₁, X₁.basicOpen f) := X₁.presheaf.map (homOfLE hfV).op (b.app V n)
    have e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact inf_eq_right.2 hle
    rw [← e]
    exact (hW.basicOpen f).basicOpen g
  have : IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme := hA
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)

end GlobalTheory.Mum
