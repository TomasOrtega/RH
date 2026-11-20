import Development.EtaleCohomology.EtaleSheaves.SysFMPfAlg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.SysFMPfAlg

namespace LateralTheory.E.SysFMPfSys

def IdemSec : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), Function.Injective (phi w) ∧ ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

/- English proof (translation)
Simplify using `only [Scheme.mem_basicOpen_top, map_sub, map_one]`. Establish `he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s)` using `hs.map _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h`.

Introduce `h h'`. Establish `hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0`. Rewrite using `[mul_sub, mul_one, he.eq, sub_self]`. Conclude with `not_isUnit_zero (hz ▸ h'.mul h)`.
-/
theorem basicOpen_one_sub {X : Scheme.{0}} {s : Γ(X, ⊤)} (hs : IsIdempotentElem s) (x : X) :
    x ∉ X.basicOpen s ↔ x ∈ X.basicOpen (1 - s) := by
  simp only [Scheme.mem_basicOpen_top, map_sub, map_one]
  have he : IsIdempotentElem (X.presheaf.germ ⊤ x trivial s) := hs.map _
  constructor
  · intro h
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left h
  · intro h h'
    have hz : X.presheaf.germ ⊤ x trivial s * (1 - X.presheaf.germ ⊤ x trivial s) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    exact not_isUnit_zero (hz ▸ h'.mul h)

/- English proof (translation)
Introduce `P _ _ W _ w hW y`. Take `⟨hinj, hrg⟩` from `hI W w`. Establish `hid : ∀ s, IsIdempotentElem (phi w s) → IsIdempotentElem s` using `fun s h => hinj (by rw [map_mul]; exact h.eq)`. Set `F : Set W` to `{e | IsIdempotentElem e ∧ ∃ s, phi w s = e ∧ y ∈ w.normalization.basicOpen s}`. Establish `hF0 : (0 : W) ∉ F`.

Introduce and unpack `⟨-, s, hs, hy⟩`. Establish `: s = 0` using `hinj (by rw [hs, map_zero])`. Substitute `this` using the available equality. Simplify using `at hy`. Establish `hFu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F`.

Introduce `e he`. Take `⟨s, rfl⟩` from `hrg e he`. Distinguish the cases in `hy : y ∈ w.normalization.basicOpen s`. Conclude with `Or.inl ⟨he, s, rfl, hy⟩`. Conclude with `Or.inr ⟨he.one_sub, 1 - s, by rw [map_sub, map_one], (basicOpen_one_sub (hid s he) y).1 hy⟩`.

Establish `hFm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F`. Introduce and unpack `e ⟨he, s, rfl, hs⟩ f ⟨hf, t, rfl, ht⟩`. Conclude with `⟨he.mul hf, s * t, map_mul _ _ _, by rw [Scheme.basicOpen_mul]; exact ⟨hs, ht⟩⟩`. Take `⟨q, hq⟩` from `prime_of_filter hW F (fun e h => h.1) hF0 hFu hFm`. Set `J : Type` to `{s : Γ(w.normalization, ⊤) // IsIdempotentElem (phi w s) ∧ phi w s ∉ q.asIdeal}`.

Use `letI : Preorder J := Preorder.lift (fun s : J => w.normalization.basicOpen s.1)`. Establish `hmono : Monotone (fun s : J => w.normalization.basicOpen s.1)` using `fun _ _ h => h`. Establish `hne : Nonempty J` using `⟨⟨1, by rw [map_one]; exact IsIdempotentElem.one, by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 q.2.ne_top⟩⟩`. Use `haveI : IsCodirectedOrder J := by`. Use `⟨?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩`. Use `⟨⟨s * t, by rw [map_mul]; exact hs1.mul ht1, by rw [map_mul]; exact q.2.mul_notMem hs2 ht2⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen s`. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `inf_le_left`.

Use `show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen t`. Rewrite using `[Scheme.basicOpen_mul]`. Conclude with `inf_le_right`. Use `haveI : IsCofiltered J := { nonempty := hne }`. Set `D : J ⥤ Scheme.{0}` to `hmono.functor ⋙ w.normalization.restrictFunctor ⋙ Over.forget _`.

Establish `hDι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ (w.normalization.basicOpen k.1).ι = (w.normalization.basicOpen j.1).ι` using `fun f => Over.w (w.normalization.restrictFunctor.map (hmono.functor.map f))`. Set `ι : ∀ j : J, D.obj j ⟶ w.normalization` to `fun j => (w.normalization.basicOpen j.1).ι`. Establish `hr : ∀ j : J, Set.range (ι j) = (w.normalization.basicOpen j.1 : Set w.normalization)` using `fun j => Scheme.Opens.range_ι _`. Use `⟨q, J, inferInstance, inferInstance, D, ι, fun j => ⟨show IsOpenImmersion (w.normalization.basicOpen j.1).ι from inferInstance, isClosedImmersion_basicOpen_idem (hid _ j.2.1), ?_⟩, fun {j k} f => ⟨hDι f, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Take `⟨-, s, hs, hy⟩` from `(hq _ j.2.1).1 j.2.2`. Rewrite `hy` using `[hinj hs]`. Then use the resulting hypothesis. Establish `hk : IsClosedImmersion (ι k)` using `isClosedImmersion_basicOpen_idem (hid _ k.2.1)`. Establish `hc : IsClosedImmersion (D.map f ≫ ι k)`. Rewrite using `[hDι f]`.

Conclude with `isClosedImmersion_basicOpen_idem (hid _ j.2.1)`. Use `@IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (D.map f) (ι k) hk hc` as an intermediate fact. Use `infer_instance`. Use extensionality with `x`. Simplify using `only [Set.mem_iInter, hr, RR, Set.mem_setOf_eq, SetLike.mem_coe]`.

Conclude with `⟨fun h s h1 h2 => h ⟨s, h1, h2⟩, fun h j => h j.1 j.2.1 j.2.2⟩`.
-/
theorem Sys_of (hI : IdemSec) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨hinj, hrg⟩ := hI W w
  have hid : ∀ s, IsIdempotentElem (phi w s) → IsIdempotentElem s := fun s h =>
    hinj (by rw [map_mul]; exact h.eq)
  let F : Set W := {e | IsIdempotentElem e ∧ ∃ s, phi w s = e ∧ y ∈ w.normalization.basicOpen s}
  have hF0 : (0 : W) ∉ F := by
    rintro ⟨-, s, hs, hy⟩
    have : s = 0 := hinj (by rw [hs, map_zero])
    subst this
    simp at hy
  have hFu : ∀ e, IsIdempotentElem e → e ∈ F ∨ 1 - e ∈ F := by
    intro e he
    obtain ⟨s, rfl⟩ := hrg e he
    by_cases hy : y ∈ w.normalization.basicOpen s
    · exact Or.inl ⟨he, s, rfl, hy⟩
    · exact Or.inr ⟨he.one_sub, 1 - s, by rw [map_sub, map_one], (basicOpen_one_sub (hid s he) y).1 hy⟩
  have hFm : ∀ e ∈ F, ∀ f ∈ F, e * f ∈ F := by
    rintro e ⟨he, s, rfl, hs⟩ f ⟨hf, t, rfl, ht⟩
    exact ⟨he.mul hf, s * t, map_mul _ _ _, by rw [Scheme.basicOpen_mul]; exact ⟨hs, ht⟩⟩
  obtain ⟨q, hq⟩ := prime_of_filter hW F (fun e h => h.1) hF0 hFu hFm
  let J : Type := {s : Γ(w.normalization, ⊤) // IsIdempotentElem (phi w s) ∧ phi w s ∉ q.asIdeal}
  letI : Preorder J := Preorder.lift (fun s : J => w.normalization.basicOpen s.1)
  have hmono : Monotone (fun s : J => w.normalization.basicOpen s.1) := fun _ _ h => h
  have hne : Nonempty J := ⟨⟨1, by rw [map_one]; exact IsIdempotentElem.one, by rw [map_one]; exact (Ideal.ne_top_iff_one _).1 q.2.ne_top⟩⟩
  haveI : IsCodirectedOrder J := by
    refine ⟨?_⟩
    rintro ⟨s, hs1, hs2⟩ ⟨t, ht1, ht2⟩
    refine ⟨⟨s * t, by rw [map_mul]; exact hs1.mul ht1, by rw [map_mul]; exact q.2.mul_notMem hs2 ht2⟩, ?_, ?_⟩
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen s
      rw [Scheme.basicOpen_mul]; exact inf_le_left
    · show w.normalization.basicOpen (s * t) ≤ w.normalization.basicOpen t
      rw [Scheme.basicOpen_mul]; exact inf_le_right
  haveI : IsCofiltered J := { nonempty := hne }
  let D : J ⥤ Scheme.{0} := hmono.functor ⋙ w.normalization.restrictFunctor ⋙ Over.forget _
  have hDι : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ (w.normalization.basicOpen k.1).ι = (w.normalization.basicOpen j.1).ι :=
    fun f => Over.w (w.normalization.restrictFunctor.map (hmono.functor.map f))
  let ι : ∀ j : J, D.obj j ⟶ w.normalization := fun j => (w.normalization.basicOpen j.1).ι
  have hr : ∀ j : J, Set.range (ι j) = (w.normalization.basicOpen j.1 : Set w.normalization) := fun j =>
    Scheme.Opens.range_ι _
  refine ⟨q, J, inferInstance, inferInstance, D, ι, fun j => ⟨show IsOpenImmersion (w.normalization.basicOpen j.1).ι from
    inferInstance, isClosedImmersion_basicOpen_idem (hid _ j.2.1), ?_⟩, fun {j k} f => ⟨hDι f, ?_⟩, ?_⟩
  · rw [hr]
    obtain ⟨-, s, hs, hy⟩ := (hq _ j.2.1).1 j.2.2
    rwa [hinj hs] at hy
  · have hk : IsClosedImmersion (ι k) := isClosedImmersion_basicOpen_idem (hid _ k.2.1)
    have hc : IsClosedImmersion (D.map f ≫ ι k) := by
      rw [hDι f]; exact isClosedImmersion_basicOpen_idem (hid _ j.2.1)
    have := @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ (D.map f) (ι k) hk hc
    infer_instance
  · ext x
    simp only [Set.mem_iInter, hr, RR, Set.mem_setOf_eq, SetLike.mem_coe]
    exact ⟨fun h s h1 h2 => h ⟨s, h1, h2⟩, fun h j => h j.1 j.2.1 j.2.2⟩

/- English proof (translation)
The claim follows from `LateralTheory.E.SysFMPf.SysFM_of (Sys_of hI) hE hR`.
-/
theorem SysFM_of (hI : IdemSec) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM :=
  LateralTheory.E.SysFMPf.SysFM_of (Sys_of hI) hE hR

end LateralTheory.E.SysFMPfSys
