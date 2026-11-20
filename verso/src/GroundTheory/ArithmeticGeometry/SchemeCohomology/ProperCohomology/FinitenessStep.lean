import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.IrreducibleImage
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RestrictIso
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionBasis
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SectionTensor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackUnit
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Annihilator
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelativeSerre
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ExistsChow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

/- English proof (translation)
The claim follows from `inferInstance`.
-/
lemma isClosedImmersion_of_isIso' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsClosedImmersion f :=
  inferInstance

/- English proof (translation)
Use `⟨isQuasicoherent_unit X, fun U _ => ?_⟩` and prove the remaining obligations. Set `one : Γ(𝟙_ X.Modules, U)` to `(1 : Γ(X, U))`. Use `⟨⟨{one}, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `m _`.

Establish `hm : m = (show Γ(X, U) from m) • one` using `(mul_one (show Γ(X, U) from m)).symm`. Rewrite using `[hm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self _)))`.
-/
theorem isCoherent_unit (X : Scheme.{u}) : IsCoherent (𝟙_ X.Modules) := by
  refine ⟨isQuasicoherent_unit X, fun U _ => ?_⟩
  let one : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have hm : m = (show Γ(X, U) from m) • one := (mul_one (show Γ(X, U) from m)).symm
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_singleton_self _)))

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))`. Use `hF.1` as an intermediate fact. Take `⟨I, hIT, G, hG, ⟨e⟩⟩` from `exists_pushforward_iso_of_supportedIn F hF hT hFT`. Establish `hFI : Scheme.Modules.SupportedIn F (I.support : Set X)`.

Establish `h` using `(Scheme.Modules.SupportedIn.univ G).pushforward I.subschemeι`. Rewrite `h` using `[Set.image_univ, Scheme.IdealSheafData.range_subschemeι]`. Conclude with `h.of_iso e`. Distinguish the cases in `hST : (I.support : Set X) = T`. Use `swap`.

Conclude with `IH _ I.support.isClosed (lt_of_le_of_ne hIT hST) F hF hFI`. Break down `isEmpty_or_nonempty I.subscheme with hZ | hZ` into its components or cases. Establish `h0 : (I.support : Set X) = ∅`. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι]`. Conclude with `Set.range_eq_empty _`.

Conclude with `FiniteH.of_isZero A (Scheme.Modules.SupportedIn.isZero_of_empty (h0 ▸ hFI))`. Use `set Z := I.subscheme`. Use `set j : Z ⟶ X := I.subschemeι`. Set `_ : Z.Over (Spec (.of A))` to `⟨j ≫ (X ↘ Spec (.of A))⟩`. Establish `: IsProper (Z ↘ Spec (.of A))` using `(inferInstance : IsProper (j ≫ (X ↘ Spec (.of A))))`.

Establish `: IsLocallyNoetherian Z` using `LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of A))`. Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of A))`. Establish `: IsNoetherian Z` using `⟨⟩`. Take `⟨Z₁, c, O, hc, hirr, hOne, hcO⟩` from `exists_irreducible_isIso_restrict Z`. Set `_ : Z₁.Over (Spec (.of A))` to `⟨c ≫ (Z ↘ Spec (.of A))⟩`.

Establish `: IsProper (Z₁ ↘ Spec (.of A))` using `(inferInstance : IsProper (c ≫ (Z ↘ Spec (.of A))))`. Take `⟨N, Z', i, π, U₁, hi, hiπ, hU₁, hπU⟩` from `exists_chow (A := A) Z₁`. Use `set ψ : Z' ⟶ X := π ≫ c ≫ j with hψ`. Set `_ : Z'.Over (Spec (.of A))` to `⟨ψ ≫ (X ↘ Spec (.of A))⟩`. Establish `: ψ.IsOver (Spec (.of A))` using `⟨rfl⟩`.

Establish `: i.IsOver (Spec (.of A))` using `⟨by`. Express the relevant statement in the definitionally equal form `i ≫ ProjSpace.toSpecBase A N = (π ≫ c ≫ j) ≫ (X ↘ Spec (.of A))`. Rewrite using `[hiπ]`. Simplify using `only [Category.assoc]`. Use the proof step `rfl⟩`.

Establish `hZ'p : IsProper (ψ ≫ (X ↘ Spec (.of A)))`. Establish `h : ψ ≫ (X ↘ Spec (.of A)) = i ≫ ProjSpace.toSpecBase A N` using `(CategoryTheory.comp_over i (Spec (.of A))).symm`. Rewrite using `[h]`. Use `infer_instance`. Establish `: IsProper ψ` using `IsProper.of_comp ψ (X ↘ Spec (.of A))`.

Establish `: IsClosedImmersion (c ≫ j)` using `inferInstance`. Establish `hG' : IsCoherent ((Scheme.Modules.pullback ψ).obj F)` using `isCoherent_pullback ψ hF`. Use `set G' := (Scheme.Modules.pullback ψ).obj F`. Take `⟨n₀, hn₀⟩` from `ProjScheme.exists_relativeSerre i ψ G' hG'`. Take `⟨n₁, hn₁⟩` from `ProjScheme.exists_generatingSections_twist i (𝟙_ Z'.Modules) (isCoherent_unit Z')`.

Use `set n := max n₀ n₁`. Take `⟨σ, hσ⟩` from `hn₁ n (le_max_right _ _)`. Use `set L := ProjScheme.twistingSheaf i (n : ℤ)`. Establish `eL : ProjScheme.twist i (𝟙_ Z'.Modules) (n : ℤ) ≅ L` using `λ_ L`. Take `⟨σL, hσL⟩` from `exists_generatingSections_of_iso eL ⟨σ, hσ⟩`.

Use `isQuasicoherent_unit Z'` as an intermediate fact. Establish `: L.IsQuasicoherent` using `(SheafOfModules.isQuasicoherent Z'.ringCatSheaf).prop_of_iso eL (ProjScheme.isQuasicoherent_twist i (𝟙_ Z'.Modules) (n : ℤ))`. Establish `hL : IsInvertibleSheaf L` using `ProjScheme.isInvertibleSheaf_twistingSheaf i (n : ℤ)`. Establish `hcO' : ((c ⁻¹ᵁ O : Z₁.Opens) : Set Z₁).Nonempty`. Take `⟨o, ho⟩` from `hOne`.

Take `⟨z, hz, -⟩` from `exists_preimage_of_isIso_morphismRestrict c ho`. Conclude with `⟨z, hz⟩`. Take `⟨z, hzU, hzO⟩` from `nonempty_preirreducible_inter U₁.isOpen (c ⁻¹ᵁ O).isOpen hU₁ hcO'`. Take `⟨y, hyU, hyz⟩` from `exists_preimage_of_isIso_morphismRestrict π hzU`. Take `⟨k, W', hyW', hbasis⟩` from `exists_isBasisOn_generatingSection L hL σL y`.

Use `set s : Γ(L, ⊤) := (σL.s k).val (op ⊤)`. Use `set Φ := (Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G' n)`. Set `α : F ⟶ Φ` to `(Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F ≫ (Scheme.Modules.pushforward ψ).map (mulSection G' L s)`. Use `set Wg : Z'.Opens := W' ⊓ π ⁻¹ᵁ (U₁ ⊓ c ⁻¹ᵁ O)`. Use `set Bad : Set X := ψ.base '' (Wg : Set Z')ᶜ ∪ j.base '' (O : Set Z)ᶜ ∪ (c ≫ j).base '' (U₁ : Set Z₁)ᶜ`.

Establish `hBad : IsClosed Bad` using `((ψ.isClosedMap _ Wg.isOpen.isClosed_compl).union (j.isClosedMap _ O.isOpen.isClosed_compl)).union ((c ≫ j).isClosedMap _ U₁.isOpen.isClosed_compl)`. Take `⟨W, hWdef⟩ : ∃ W : X.Opens, (W : Set X) = Badᶜ` from `⟨⟨Badᶜ, hBad.isOpen_compl⟩, rfl⟩`. Establish `hcjinj : Function.Injective (c ≫ j).base` using `(c ≫ j).isClosedEmbedding.injective`. Establish `hjinj : Function.Injective j.base` using `j.isClosedEmbedding.injective`. Establish `hψy : ψ.base y = (c ≫ j).base (π.base y)` using `rfl`.

Establish `hyWg : y ∈ Wg` using `⟨hyW', by`. Express the relevant statement in the definitionally equal form `π.base y ∈ U₁ ⊓ c ⁻¹ᵁ O`. Rewrite using `[hyz]`. Conclude with `⟨hzU, hzO⟩⟩`. Establish `hxW : ψ.base y ∈ W`.

Express the relevant statement in the definitionally equal form `ψ.base y ∈ (W : Set X)`. Rewrite using `[hWdef]`. Introduce and unpack `((⟨y', hy', hyy'⟩ | ⟨o, ho, hoy⟩) | ⟨z', hz', hzy⟩)`. Establish `h1 : π.base y' = π.base y` using `hcjinj hyy'`. Establish `hy'U : y' ∈ π ⁻¹ᵁ U₁`.

Express the relevant statement in the definitionally equal form `π.base y' ∈ U₁`. Rewrite using `[h1, hyz]`. Conclude with `hzU`. Conclude with `hy' (injOn_of_isIso_morphismRestrict π hy'U hyU h1 ▸ hyWg)`. Establish `h1 : o = c.base (π.base y)` using `hjinj hoy`.

Apply `ho` to reduce the goal to its premises. Rewrite using `[h1, hyz]`. Conclude with `hzO`. Establish `h1 : z' = π.base y` using `hcjinj hzy`. Apply `hz'` to reduce the goal to its premises.

Rewrite using `[h1, hyz]`. Conclude with `hzU`. Establish `hψW : ψ ⁻¹ᵁ W ≤ Wg` using `fun y' hy' => by`. Establish `hy' : ψ.base y' ∈ (W : Set X)` using `hy'`. Rewrite `hy'` using `[hWdef]`.

Assume the negation of the conclusion as `h`. Conclude with `hy' (Or.inl (Or.inl ⟨y', h, rfl⟩))`. Establish `hjW : j ⁻¹ᵁ W ≤ O` using `fun z' hz' => by`. Establish `hz' : j.base z' ∈ (W : Set X)` using `hz'`. Rewrite `hz'` using `[hWdef]`.

Assume the negation of the conclusion as `h`. Conclude with `hz' (Or.inl (Or.inr ⟨z', h, rfl⟩))`. Establish `hcjW : (c ≫ j) ⁻¹ᵁ W ≤ U₁` using `fun z' hz' => by`. Establish `hz' : (c ≫ j).base z' ∈ (W : Set X)` using `hz'`. Rewrite `hz'` using `[hWdef]`.

Assume the negation of the conclusion as `h`. Conclude with `hz' (Or.inr ⟨z', h, rfl⟩)`. Establish `hπW : IsIso (π ∣_ ((c ≫ j) ⁻¹ᵁ W))` using `isIso_morphismRestrict_of_le π hcjW`. Establish `: IsClosedImmersion (ψ ∣_ W)`. Establish `h1 : IsClosedImmersion (π ∣_ ((c ≫ j) ⁻¹ᵁ W))` using `@isClosedImmersion_of_isIso' _ _ _ hπW`.

Establish `h2 : IsClosedImmersion ((c ≫ j) ∣_ W)` using `inferInstance`. Rewrite using `[show ψ = π ≫ (c ≫ j) from rfl, morphismRestrict_comp]`. Conclude with `@IsClosedImmersion.comp _ _ _ _ _ h1 h2`. Establish `hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 → ∀ m : Γ(F, V), a • m = 0`. Introduce `V _ hVW a ha m`.

Establish `hVc : (c ≫ j) ⁻¹ᵁ V ≤ U₁` using `(Scheme.Hom.preimage_mono _ hVW).trans hcjW`. Establish `hVj : j ⁻¹ᵁ V ≤ O` using `(Scheme.Hom.preimage_mono _ hVW).trans hjW`. Establish `hπinj` using `(bijective_app_of_isIso_morphismRestrict π hVc).1`. Establish `hcinj` using `(bijective_app_of_isIso_morphismRestrict c hVj).1`. Establish `hja : j.app V a = 0`.

Apply `hcinj` to reduce the goal to its premises. Apply `hπinj` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Take `⟨m', rfl⟩ : ∃ m', e.hom.app V m' = m` from `⟨e.inv.app V m, by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]⟩`. Establish `h0 : a • m' = 0`.

Rewrite using `[smul_pushforward, hja, zero_smul]`. Both sides reduce to the same expression. Rewrite using `[← Scheme.Modules.Hom.app_smul, h0, map_zero]`. Establish `hunit` using `bijective_unit_app_of_le ψ F W hkill`. Establish `hmul` using `bijective_mulSection_app G' L s hbasis`.

Establish `hα : ∀ V : X.Opens, V ≤ W → Function.Bijective (α.app V)` using `fun V hV => (hmul (ψ ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hV).trans (hψW.trans inf_le_left))).comp (hunit V hV)`. Take `⟨hΦcoh, hΦiso⟩` from `hn₀ n (le_max_left _ _)`. Establish `hΦ : FiniteH.{u} A Φ` using `fun p => by`. Take `⟨e'⟩` from `hΦiso p`. Use `ProjScheme.finite_H.{u} i (ProjScheme.twist i G' n) (isCoherent_tensor_of_invertible hG' hL) p` as an intermediate fact.

Conclude with `Module.Finite.equiv e'`. Establish `hxT : ψ.base y ∈ T`. Rewrite using `[← hST, ← Scheme.IdealSheafData.range_subschemeι]`. Conclude with `⟨c.base (π.base y), rfl⟩`. Establish `hT' : IsClosed (T ∩ (W : Set X)ᶜ)` using `hT.inter W.isOpen.isClosed_compl`.

Establish `hT'T : T ∩ (W : Set X)ᶜ ⊂ T` using `⟨Set.inter_subset_left, fun h => (h hxT).2 hxW⟩`. Establish `hK : FiniteH.{u} A (kernel α)`. Use `hΦcoh.1` as an intermediate fact. Use `IH _ hT' hT'T (kernel α) (isCoherent_kernel α hF) ((hFT.of_mono (kernel.ι α)).inter (kernel_supportedIn α W hα) hT W.isOpen.isClosed_compl)`. Establish `hΦT : Scheme.Modules.SupportedIn Φ T`.

Use `((Scheme.Modules.SupportedIn.univ _).pushforward ψ).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y', -, rfl⟩`. Rewrite using `[← hST, ← Scheme.IdealSheafData.range_subschemeι]`. Conclude with `⟨c.base (π.base y'), rfl⟩`. Establish `hC : FiniteH.{u} A (cokernel α)` using `IH _ hT' hT'T (cokernel α) (isCoherent_cokernel α hΦcoh) ((hΦT.of_epi (cokernel.π α)).inter (cokernel_supportedIn α W hα) hT W.isOpen.isClosed_compl)`.

Conclude with `FiniteH.of_shortExact₂ (kerCoimSC_shortExact α) hK (FiniteH.of_shortExact₁ (coimCokSC_shortExact α) hΦ hC)`.
-/
theorem finiteH_step
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))]
    (T : Set X) (hT : IsClosed T)
    (IH : ∀ T' : Set X, IsClosed T' → T' ⊂ T → ∀ F : X.Modules, IsCoherent F →
      Scheme.Modules.SupportedIn F T' → FiniteH.{u} A F)
    (F : X.Modules) (hF : IsCoherent F) (hFT : Scheme.Modules.SupportedIn F T) :
    FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := hF.1
  obtain ⟨I, hIT, G, hG, ⟨e⟩⟩ := exists_pushforward_iso_of_supportedIn F hF hT hFT
  have hFI : Scheme.Modules.SupportedIn F (I.support : Set X) := by
    have h := (Scheme.Modules.SupportedIn.univ G).pushforward I.subschemeι
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at h
    exact h.of_iso e
  by_cases hST : (I.support : Set X) = T
  swap
  · exact IH _ I.support.isClosed (lt_of_le_of_ne hIT hST) F hF hFI
  rcases isEmpty_or_nonempty I.subscheme with hZ | hZ
  · have h0 : (I.support : Set X) = ∅ := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.range_eq_empty _
    exact FiniteH.of_isZero A (Scheme.Modules.SupportedIn.isZero_of_empty (h0 ▸ hFI))
  set Z := I.subscheme
  set j : Z ⟶ X := I.subschemeι
  let _ : Z.Over (Spec (.of A)) := ⟨j ≫ (X ↘ Spec (.of A))⟩
  have : IsProper (Z ↘ Spec (.of A)) := (inferInstance : IsProper (j ≫ (X ↘ Spec (.of A))))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of A))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of A))
  have : IsNoetherian Z := ⟨⟩
  obtain ⟨Z₁, c, O, hc, hirr, hOne, hcO⟩ := exists_irreducible_isIso_restrict Z
  let _ : Z₁.Over (Spec (.of A)) := ⟨c ≫ (Z ↘ Spec (.of A))⟩
  have : IsProper (Z₁ ↘ Spec (.of A)) := (inferInstance : IsProper (c ≫ (Z ↘ Spec (.of A))))
  obtain ⟨N, Z', i, π, U₁, hi, hiπ, hU₁, hπU⟩ := exists_chow (A := A) Z₁
  set ψ : Z' ⟶ X := π ≫ c ≫ j with hψ
  let _ : Z'.Over (Spec (.of A)) := ⟨ψ ≫ (X ↘ Spec (.of A))⟩
  have : ψ.IsOver (Spec (.of A)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of A)) := ⟨by
    change i ≫ ProjSpace.toSpecBase A N = (π ≫ c ≫ j) ≫ (X ↘ Spec (.of A))
    rw [hiπ]
    simp only [Category.assoc]
    rfl⟩
  have hZ'p : IsProper (ψ ≫ (X ↘ Spec (.of A))) := by
    have h : ψ ≫ (X ↘ Spec (.of A)) = i ≫ ProjSpace.toSpecBase A N :=
      (CategoryTheory.comp_over i (Spec (.of A))).symm
    rw [h]
    infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (X ↘ Spec (.of A))
  have : IsClosedImmersion (c ≫ j) := inferInstance

  have hG' : IsCoherent ((Scheme.Modules.pullback ψ).obj F) := isCoherent_pullback ψ hF
  set G' := (Scheme.Modules.pullback ψ).obj F
  obtain ⟨n₀, hn₀⟩ := ProjScheme.exists_relativeSerre i ψ G' hG'
  obtain ⟨n₁, hn₁⟩ := ProjScheme.exists_generatingSections_twist i (𝟙_ Z'.Modules)
    (isCoherent_unit Z')
  set n := max n₀ n₁
  obtain ⟨σ, hσ⟩ := hn₁ n (le_max_right _ _)
  set L := ProjScheme.twistingSheaf i (n : ℤ)
  have eL : ProjScheme.twist i (𝟙_ Z'.Modules) (n : ℤ) ≅ L := λ_ L
  obtain ⟨σL, hσL⟩ := exists_generatingSections_of_iso eL ⟨σ, hσ⟩
  have := isQuasicoherent_unit Z'
  have : L.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z'.ringCatSheaf).prop_of_iso eL
      (ProjScheme.isQuasicoherent_twist i (𝟙_ Z'.Modules) (n : ℤ))
  have hL : IsInvertibleSheaf L := ProjScheme.isInvertibleSheaf_twistingSheaf i (n : ℤ)

  have hcO' : ((c ⁻¹ᵁ O : Z₁.Opens) : Set Z₁).Nonempty := by
    obtain ⟨o, ho⟩ := hOne
    obtain ⟨z, hz, -⟩ := exists_preimage_of_isIso_morphismRestrict c ho
    exact ⟨z, hz⟩
  obtain ⟨z, hzU, hzO⟩ := nonempty_preirreducible_inter U₁.isOpen (c ⁻¹ᵁ O).isOpen hU₁ hcO'
  obtain ⟨y, hyU, hyz⟩ := exists_preimage_of_isIso_morphismRestrict π hzU
  obtain ⟨k, W', hyW', hbasis⟩ := exists_isBasisOn_generatingSection L hL σL y
  set s : Γ(L, ⊤) := (σL.s k).val (op ⊤)
  set Φ := (Scheme.Modules.pushforward ψ).obj (ProjScheme.twist i G' n)
  let α : F ⟶ Φ := (Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F ≫
    (Scheme.Modules.pushforward ψ).map (mulSection G' L s)

  set Wg : Z'.Opens := W' ⊓ π ⁻¹ᵁ (U₁ ⊓ c ⁻¹ᵁ O)
  set Bad : Set X := ψ.base '' (Wg : Set Z')ᶜ ∪ j.base '' (O : Set Z)ᶜ ∪
    (c ≫ j).base '' (U₁ : Set Z₁)ᶜ
  have hBad : IsClosed Bad :=
    ((ψ.isClosedMap _ Wg.isOpen.isClosed_compl).union
      (j.isClosedMap _ O.isOpen.isClosed_compl)).union
      ((c ≫ j).isClosedMap _ U₁.isOpen.isClosed_compl)
  obtain ⟨W, hWdef⟩ : ∃ W : X.Opens, (W : Set X) = Badᶜ := ⟨⟨Badᶜ, hBad.isOpen_compl⟩, rfl⟩
  have hcjinj : Function.Injective (c ≫ j).base := (c ≫ j).isClosedEmbedding.injective
  have hjinj : Function.Injective j.base := j.isClosedEmbedding.injective
  have hψy : ψ.base y = (c ≫ j).base (π.base y) := rfl
  have hyWg : y ∈ Wg := ⟨hyW', by
    change π.base y ∈ U₁ ⊓ c ⁻¹ᵁ O
    rw [hyz]
    exact ⟨hzU, hzO⟩⟩
  have hxW : ψ.base y ∈ W := by
    change ψ.base y ∈ (W : Set X)
    rw [hWdef]
    rintro ((⟨y', hy', hyy'⟩ | ⟨o, ho, hoy⟩) | ⟨z', hz', hzy⟩)
    · have h1 : π.base y' = π.base y := hcjinj hyy'
      have hy'U : y' ∈ π ⁻¹ᵁ U₁ := by
        change π.base y' ∈ U₁
        rw [h1, hyz]
        exact hzU
      exact hy' (injOn_of_isIso_morphismRestrict π hy'U hyU h1 ▸ hyWg)
    · have h1 : o = c.base (π.base y) := hjinj hoy
      apply ho
      rw [h1, hyz]
      exact hzO
    · have h1 : z' = π.base y := hcjinj hzy
      apply hz'
      rw [h1, hyz]
      exact hzU
  have hψW : ψ ⁻¹ᵁ W ≤ Wg := fun y' hy' => by
    have hy' : ψ.base y' ∈ (W : Set X) := hy'
    rw [hWdef] at hy'
    by_contra h
    exact hy' (Or.inl (Or.inl ⟨y', h, rfl⟩))
  have hjW : j ⁻¹ᵁ W ≤ O := fun z' hz' => by
    have hz' : j.base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inl (Or.inr ⟨z', h, rfl⟩))
  have hcjW : (c ≫ j) ⁻¹ᵁ W ≤ U₁ := fun z' hz' => by
    have hz' : (c ≫ j).base z' ∈ (W : Set X) := hz'
    rw [hWdef] at hz'
    by_contra h
    exact hz' (Or.inr ⟨z', h, rfl⟩)

  have hπW : IsIso (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) := isIso_morphismRestrict_of_le π hcjW
  have : IsClosedImmersion (ψ ∣_ W) := by
    have h1 : IsClosedImmersion (π ∣_ ((c ≫ j) ⁻¹ᵁ W)) :=
      @isClosedImmersion_of_isIso' _ _ _ hπW
    have h2 : IsClosedImmersion ((c ≫ j) ∣_ W) := inferInstance
    rw [show ψ = π ≫ (c ≫ j) from rfl, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ h1 h2

  have hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 →
      ∀ m : Γ(F, V), a • m = 0 := by
    intro V _ hVW a ha m
    have hVc : (c ≫ j) ⁻¹ᵁ V ≤ U₁ := (Scheme.Hom.preimage_mono _ hVW).trans hcjW
    have hVj : j ⁻¹ᵁ V ≤ O := (Scheme.Hom.preimage_mono _ hVW).trans hjW
    have hπinj := (bijective_app_of_isIso_morphismRestrict π hVc).1
    have hcinj := (bijective_app_of_isIso_morphismRestrict c hVj).1
    have hja : j.app V a = 0 := by
      apply hcinj
      apply hπinj
      calc _ = (ψ.app V) a := rfl
        _ = 0 := ha
        _ = _ := by rw [map_zero]; exact (map_zero _).symm
    obtain ⟨m', rfl⟩ : ∃ m', e.hom.app V m' = m :=
      ⟨e.inv.app V m, by rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
        e.inv_hom_id, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]⟩
    have h0 : a • m' = 0 := by
      rw [smul_pushforward, hja, zero_smul]
      rfl
    rw [← Scheme.Modules.Hom.app_smul, h0, map_zero]
  have hunit := bijective_unit_app_of_le ψ F W hkill
  have hmul := bijective_mulSection_app G' L s hbasis
  have hα : ∀ V : X.Opens, V ≤ W → Function.Bijective (α.app V) := fun V hV =>
    (hmul (ψ ⁻¹ᵁ V) ((Scheme.Hom.preimage_mono _ hV).trans (hψW.trans inf_le_left))).comp
      (hunit V hV)

  obtain ⟨hΦcoh, hΦiso⟩ := hn₀ n (le_max_left _ _)
  have hΦ : FiniteH.{u} A Φ := fun p => by
    obtain ⟨e'⟩ := hΦiso p
    have := ProjScheme.finite_H.{u} i (ProjScheme.twist i G' n)
      (isCoherent_tensor_of_invertible hG' hL) p
    exact Module.Finite.equiv e'

  have hxT : ψ.base y ∈ T := by
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y), rfl⟩
  have hT' : IsClosed (T ∩ (W : Set X)ᶜ) := hT.inter W.isOpen.isClosed_compl
  have hT'T : T ∩ (W : Set X)ᶜ ⊂ T :=
    ⟨Set.inter_subset_left, fun h => (h hxT).2 hxW⟩
  have hK : FiniteH.{u} A (kernel α) :=
    have := hΦcoh.1
    IH _ hT' hT'T (kernel α) (isCoherent_kernel α hF)
      ((hFT.of_mono (kernel.ι α)).inter (kernel_supportedIn α W hα) hT W.isOpen.isClosed_compl)
  have hΦT : Scheme.Modules.SupportedIn Φ T := by
    refine ((Scheme.Modules.SupportedIn.univ _).pushforward ψ).mono ?_
    rintro _ ⟨y', -, rfl⟩
    rw [← hST, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c.base (π.base y'), rfl⟩
  have hC : FiniteH.{u} A (cokernel α) :=
    IH _ hT' hT'T (cokernel α) (isCoherent_cokernel α hΦcoh)
      ((hΦT.of_epi (cokernel.π α)).inter (cokernel_supportedIn α W hα) hT
        W.isOpen.isClosed_compl)
  exact FiniteH.of_shortExact₂ (kerCoimSC_shortExact α) hK
    (FiniteH.of_shortExact₁ (coimCokSC_shortExact α) hΦ hC)

/- English proof (translation)
Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))`. Establish `: IsNoetherian X` using `⟨⟩`. Proceed by induction on `T using WellFoundedLT.induction with`. Consider the case `_ T IH`.

Introduce `F hF hFT`. Use `finiteH_step X T T.isClosed (fun T' hT' hlt F' hF' hF'T' => ?_) F hF hFT` and prove the remaining obligations. Conclude with `IH ⟨T', hT'⟩ hlt F' hF' hF'T'`.
-/
theorem finiteH_of_supportedIn
    (X : Scheme.{u}) [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (T : Closeds X) :
    ∀ F : X.Modules, IsCoherent F → Scheme.Modules.SupportedIn F T → FiniteH.{u} A F := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have : IsNoetherian X := ⟨⟩
  induction T using WellFoundedLT.induction with
  | _ T IH =>
    intro F hF hFT
    refine finiteH_step X T T.isClosed (fun T' hT' hlt F' hF' hF'T' => ?_) F hF hFT
    exact IH ⟨T', hT'⟩ hlt F' hF' hF'T'

end

end GroundTheory.Arith.SchemeCoh
