import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory.SubschemeIntegral

/- English proof (translation)
Introduce `u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩`. Take `⟨a, hxa⟩` from `hcov x`. Take `⟨b, hyb⟩` from `hcov y`. Take `⟨z, hza, hzu, hzb⟩` from `hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩ (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)`. Take `⟨w, _, hw⟩` from `hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩`.

Conclude with `⟨w, trivial, hw⟩`.
-/
theorem isPreirreducible_univ_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ a, IsOpen (U a)) (hcov : ∀ x, ∃ a, x ∈ U a) (hirr : ∀ a, IsPreirreducible (U a))
    (hmeet : ∀ a b, (U a).Nonempty → (U b).Nonempty → (U a ∩ U b).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨a, hxa⟩ := hcov x
  obtain ⟨b, hyb⟩ := hcov y
  obtain ⟨z, hza, hzu, hzb⟩ := hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩
    (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)
  obtain ⟨w, _, hw⟩ := hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩
  exact ⟨w, trivial, hw⟩

/- English proof (translation)
Establish `hmem : hU.fromSpec P ∈ U.1`. Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨P, rfl⟩`. Express the relevant statement in the definitionally equal form `hU.fromSpec P ∈ I.support`. Rewrite using `[Scheme.IdealSheafData.mem_support_iff_of_mem hmem]`.

Establish `: hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1))` using `⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩`. Rewrite `this` using `[hU.fromSpec_image_zeroLocus]`. Conclude with `this.1`.
-/
theorem fromSpec_mem_support {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (hU : IsAffineOpen U.1) (P : PrimeSpectrum Γ(Y, U.1)) (h : I.ideal U ≤ P.asIdeal) :
    hU.fromSpec P ∈ (I.support : Set Y) := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩
  change hU.fromSpec P ∈ I.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  have : hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1)) :=
    ⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩
  rw [hU.fromSpec_image_zeroLocus] at this
  exact this.1

/- English proof (translation)
Establish `hx : I.subschemeι x ∈ (⨆ a, (W a).1)` using `by rw [hW]; trivial`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Use `haveI := I.subschemeCover.map_prop (W a)`. Establish `: x ∈ (I.subschemeCover.f (W a)).opensRange`. Rewrite using `[Scheme.IdealSheafData.opensRange_subschemeCover_map]`.

Conclude with `ha`. Take `⟨y, hy⟩` from `this`. Conclude with `⟨a, y, hy⟩`.
-/
theorem exists_cover {Y : Scheme.{0}} (I : Y.IdealSheafData) {ι : Type} (W : ι → Y.affineOpens)
    (hW : ⨆ a, (W a).1 = ⊤) (x : I.subscheme) :
    ∃ a y, (I.subschemeCover.f (W a)) y = x := by
  have hx : I.subschemeι x ∈ (⨆ a, (W a).1) := by rw [hW]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  haveI := I.subschemeCover.map_prop (W a)
  have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact ha
  obtain ⟨y, hy⟩ := this
  exact ⟨a, y, hy⟩

/- English proof (translation)
Use `haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h`. Use `⟨fun y => ?_⟩` and prove the remaining obligations. Establish `: Subsingleton (I.subschemeCover.X U)` using `this`. Conclude with `y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))`.
-/
theorem isEmpty_spec_top {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (h : I.ideal U = ⊤) : IsEmpty (Spec (I.subschemeCover.X U)) := by
  haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h
  refine ⟨fun y => ?_⟩
  have : Subsingleton (I.subschemeCover.X U) := this
  exact y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))

/- English proof (translation)
Introduce `Y I ι W hW hI hm`. Distinguish the cases in `hex : ∃ a, (I.ideal (W a)).IsPrime`. Use `left`. Take `⟨a₀, ha₀⟩` from `hex`. Use `haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by`.

Introduce `a`. Break down `hI a with h | h` into its components or cases. Use `haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h`. Express the relevant statement in the definitionally equal form `_root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a))`. Use `infer_instance`.

Use `haveI := h`. Express the relevant statement in the definitionally equal form `_root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a))`. Use `infer_instance`. Set `𝒰 : I.subscheme.OpenCover` to `Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a))) (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))`. Use `haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by`.

Express the relevant statement in the definitionally equal form `AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a)))`. Use `haveI := hred a`. Use `infer_instance`. Use `haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰`. Establish `hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme, I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩`.

Introduce `a ha`. Use `fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl` as an intermediate fact. Rewrite `this` using `[← I.range_subschemeι]`. Conclude with `this`. Establish `hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a))`.

Introduce `a x hx`. Use `haveI := I.subschemeCover.map_prop (W a)`. Establish `: x ∈ (I.subschemeCover.f (W a)).opensRange`. Rewrite using `[Scheme.IdealSheafData.opensRange_subschemeCover_map]`. Conclude with `hx`.

Conclude with `this`. Establish `hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime`. Introduce and unpack `a ⟨_, y, _⟩`. Break down `hI a with h | h` into its components or cases. Conclude with `((isEmpty_spec_top I (W a) h).false y).elim`.

Conclude with `h`. Use `haveI : IrreducibleSpace I.subscheme := by`. Take `⟨x₀, -⟩` from `hpt a₀ ha₀`. Establish `hpre : IsPreirreducible (Set.univ : Set I.subscheme)`. Use `isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_) (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations.

Use `haveI := I.subschemeCover.map_prop (W a)`. Conclude with `(I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range`. Take `⟨a, y, hy⟩` from `exists_cover I W hW x`. Conclude with `⟨a, y, hy⟩`. Break down `hI a with h | h` into its components or cases.

Use `haveI := isEmpty_spec_top I (W a) h`. Rewrite using `[Set.range_eq_empty]`. Conclude with `isPreirreducible_empty`. Use `haveI : IsDomain (I.subschemeCover.X (W a)) := by`. Express the relevant statement in the definitionally equal form `IsDomain (Γ(Y, W a) ⧸ I.ideal (W a))`.

Use `haveI := h`. Use `infer_instance`. Rewrite using `[← Set.image_univ]`. Conclude with `((IrreducibleSpace.isIrreducible_univ _).image _ (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible`. Take `⟨x, hx⟩` from `hpt a (hp a ha)`.

Use `⟨x, hrange a x ?_, hrange b x ?_⟩` and prove the remaining obligations. Rewrite using `[hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]`. Conclude with `⟨_, rfl⟩`. Rewrite using `[hx]`. Conclude with `hm a b (hp a ha) (hp b hb).ne_top`.

Use `haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩`. Conclude with `{ toNonempty := ⟨x₀⟩ }`. Conclude with `isIntegral_of_irreducibleSpace_of_isReduced _`. Use `right`. Use `⟨fun x => ?_⟩` and prove the remaining obligations.

Take `⟨a, y, -⟩` from `exists_cover I W hW x`. Establish `h : I.ideal (W a) = ⊤` using `(hI a).resolve_right (fun h => hex ⟨a, h⟩)`. Conclude with `(isEmpty_spec_top I (W a) h).false y`.
-/
theorem isIntegral_or_isEmpty_subscheme : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  intro Y I ι W hW hI hm
  by_cases hex : ∃ a, (I.ideal (W a)).IsPrime
  · left
    obtain ⟨a₀, ha₀⟩ := hex
    haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by
      intro a
      rcases hI a with h | h
      · haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
      · haveI := h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
    let 𝒰 : I.subscheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a)))
      (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))
    haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by
      change AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a))); haveI := hred a; infer_instance
    haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰
    have hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme,
        I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ := by
      intro a ha
      have := fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl
      rw [← I.range_subschemeι] at this
      exact this
    have hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a)) := by
      intro a x hx
      haveI := I.subschemeCover.map_prop (W a)
      have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
        rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact hx
      exact this
    have hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime := by
      rintro a ⟨_, y, _⟩
      rcases hI a with h | h
      · exact ((isEmpty_spec_top I (W a) h).false y).elim
      · exact h
    haveI : IrreducibleSpace I.subscheme := by
      obtain ⟨x₀, -⟩ := hpt a₀ ha₀
      have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
        refine isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_)
          (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)
        · haveI := I.subschemeCover.map_prop (W a); exact (I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range
        · obtain ⟨a, y, hy⟩ := exists_cover I W hW x; exact ⟨a, y, hy⟩
        · rcases hI a with h | h
          · haveI := isEmpty_spec_top I (W a) h
            rw [Set.range_eq_empty]; exact isPreirreducible_empty
          · haveI : IsDomain (I.subschemeCover.X (W a)) := by
              change IsDomain (Γ(Y, W a) ⧸ I.ideal (W a)); haveI := h; infer_instance
            rw [← Set.image_univ]
            exact ((IrreducibleSpace.isIrreducible_univ _).image _
              (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible
        · obtain ⟨x, hx⟩ := hpt a (hp a ha)
          refine ⟨x, hrange a x ?_, hrange b x ?_⟩
          · rw [hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]; exact ⟨_, rfl⟩
          · rw [hx]; exact hm a b (hp a ha) (hp b hb).ne_top
      haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩
      exact { toNonempty := ⟨x₀⟩ }
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · right
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, -⟩ := exists_cover I W hW x
    have h : I.ideal (W a) = ⊤ := (hI a).resolve_right (fun h => hex ⟨a, h⟩)
    exact (isEmpty_spec_top I (W a) h).false y

end GlobalTheory.SubschemeIntegral
