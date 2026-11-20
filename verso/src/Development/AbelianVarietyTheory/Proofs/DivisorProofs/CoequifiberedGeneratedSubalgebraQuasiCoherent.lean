import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

/- English proof (translation)
Use `letI := ρ.toAlgebra`. Use `letI := (ρ.restrict S S' hρ).toAlgebra`. Use `.mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_` and prove the remaining obligations. Take `⟨v, hv, hsv⟩` from `hu`. Conclude with `.of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)`.

Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj (S := A') s (z : A')`. Establish `ha' : ρ a = (z : A') * ρ s ^ n` using `ha.symm`. Establish `hmem : ρ a ∈ S'` using `ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)`. Take `⟨m, hm⟩` from `hd a hmem`. Use `⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)`. Rewrite using `[map_mul, map_pow, ha', pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `h : ρ a = ρ b` using `congrArg Subtype.val hab`. Take `⟨n, hn⟩` from `IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h`.

Conclude with `⟨n, Subtype.ext (by simpa using hn)⟩`.
-/
theorem isLocalizationAway_subring {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A')
    (S : Subring A) (S' : Subring A') (hρ : ∀ a ∈ S, ρ a ∈ S') (s : A) (hs : s ∈ S)
    (hloc : letI := ρ.toAlgebra; IsLocalization.Away s A')
    (hu : ∃ v ∈ S', ρ s * v = 1) (hd : ∀ a : A, ρ a ∈ S' → ∃ m : ℕ, s ^ m * a ∈ S) :
    letI := (ρ.restrict S S' hρ).toAlgebra
    IsLocalization.Away (⟨s, hs⟩ : S) S' := by
  letI := ρ.toAlgebra
  letI := (ρ.restrict S S' hρ).toAlgebra
  refine .mk _ ?_ (fun z ↦ ?_) fun a b hab ↦ ?_
  · obtain ⟨v, hv, hsv⟩ := hu
    exact .of_mul_eq_one (⟨v, hv⟩ : S') (Subtype.ext hsv)
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := A') s (z : A')
    have ha' : ρ a = (z : A') * ρ s ^ n := ha.symm
    have hmem : ρ a ∈ S' := ha' ▸ S'.mul_mem z.2 (S'.pow_mem (hρ s hs) n)
    obtain ⟨m, hm⟩ := hd a hmem
    refine ⟨n + m, ⟨s ^ m * a, hm⟩, Subtype.ext ?_⟩
    change (z : A') * ρ s ^ (n + m) = ρ (s ^ m * a)
    rw [map_mul, map_pow, ha', pow_add]
    ring
  · have h : ρ a = ρ b := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := A') s (a := (a : A)) (b := (b : A)) h
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GlobalTheory.QcSub

namespace GlobalTheory.QcSub

/- English proof (translation)
Rewrite using `[Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]`. Introduce `U f`. Establish `hloc` using `isLocalizationAway F α hα U.2 f`. Establish `hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) = (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f)`. Use `congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)` as an intermediate fact.

Simplify using `only [CommRingCat.comp_apply] at this`. Conclude with `this.symm`. Establish `hu : ∃ v ∈ sub F α V T (X.basicOpen f), (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1`. Take `⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f), (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1` from `(X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv`. Use `⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩` and prove the remaining obligations.

Rewrite using `[hnat, ← map_mul, hw, map_one]`. Conclude with `isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha) _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)`.
-/
theorem coequifibered_subNat (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))
    (hd : ∀ W : X.Opens, IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) →
      ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W) :
    (subNat F α V T).Coequifibered := by
  rw [Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hloc := isLocalizationAway F α hα U.2 f
  have hnat : (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) =
      (α.app (op (X.basicOpen f))).hom ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
    have := congr($(α.naturality (homOfLE (X.basicOpen_le f)).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  have hu : ∃ v ∈ sub F α V T (X.basicOpen f),
      (F.map (homOfLE (X.basicOpen_le f)).op).hom ((α.app (op U.1)).hom f) * v = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : Γ(X, X.basicOpen f),
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f * w = 1 :=
      (X.toRingedSpace.isUnit_res_basicOpen f).exists_right_inv
    refine ⟨(α.app (op (X.basicOpen f))).hom w, algebraMap_mem_sub F α V T _ w, ?_⟩
    rw [hnat, ← map_mul, hw, map_one]
  exact isLocalizationAway_subring (F.map (homOfLE (X.basicOpen_le f)).op).hom
    (sub F α V T U.1) (sub F α V T (X.basicOpen f)) (fun a ha ↦ res_mem_sub F α V T _ ha)
    _ (algebraMap_mem_sub F α V T U.1 f) hloc hu (hd U.1 U.2 f)

end GlobalTheory.QcSub
