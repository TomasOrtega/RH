import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

/- English proof (translation)
Establish `h : IsIso (f.appTop)` using `(ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)`. Establish `: IsIso (Spec.map f.appTop)` using `inferInstance`. Establish `e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv`. Rewrite using `[← Category.assoc, Scheme.isoSpec_hom_naturality]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Use `infer_instance`.
-/
theorem isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance

/- English proof (translation)
Use `GlobalTheory.IsNormalScheme.of_pred hX` as an intermediate fact. Use `le_antisymm (fun z hz ↦ ?_) hle` and prove the remaining obligations. Take `⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen`. Establish `hN' : IsAffineOpen N` using `hN`. Establish `hNV' : IsAffineOpen (N ⊓ V)` using `hN'.inf hV`.

Establish `: IsAffine N` using `hN'`. Establish `: IsAffine (N ⊓ V : X.Opens)` using `hNV'`. Establish `hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N))`. Use `isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_` and prove the remaining obligations. Establish `hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1` using `by rwa [coheight_apply_of_isOpenImmersion]`.

Establish `hxV : Scheme.Opens.ι N x ∈ V` using `h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')`. Conclude with `⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩`. Take `⟨y, hy⟩` from `(X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩`. Establish `hyz : y.1 = z` using `(Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)`. Conclude with `hyz ▸ y.2.2`.
-/
theorem eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2

end GlobalTheory
