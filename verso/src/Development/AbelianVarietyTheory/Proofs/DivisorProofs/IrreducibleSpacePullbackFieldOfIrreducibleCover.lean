import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `{ isPreirreducible_univ := ?_, toNonempty := inferInstance }` and prove the remaining obligations. Introduce `u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩`. Take `⟨Wx, hWx, hxW⟩` from `hcov x`. Take `⟨Wy, hWy, hyW⟩` from `hcov y`. Take `⟨w, hwx, hwu, hwy⟩` from `hirr Wx hWx u Wy hu (hopen Wy hWy) ⟨x, hxW, hxu⟩ (hmeet Wx hWx Wy hWy)`.

Take `⟨z, hzW, hz⟩` from `hirr Wy hWy u v hu hv ⟨w, hwy, hwu⟩ ⟨y, hyW, hyv⟩`. Conclude with `⟨z, trivial, hz⟩`.
-/
theorem irreducibleSpace_of_open_cover_meeting {P : Type} [TopologicalSpace P] [Nonempty P]
    (S : Set (Set P)) (hopen : ∀ W ∈ S, IsOpen W) (hirr : ∀ W ∈ S, IsPreirreducible W)
    (hcov : ∀ p : P, ∃ W ∈ S, p ∈ W) (hmeet : ∀ W ∈ S, ∀ W' ∈ S, (W ∩ W').Nonempty) :
    IrreducibleSpace P := by
  refine { isPreirreducible_univ := ?_, toNonempty := inferInstance }
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨Wx, hWx, hxW⟩ := hcov x
  obtain ⟨Wy, hWy, hyW⟩ := hcov y
  obtain ⟨w, hwx, hwu, hwy⟩ :=
    hirr Wx hWx u Wy hu (hopen Wy hWy) ⟨x, hxW, hxu⟩ (hmeet Wx hWx Wy hWy)
  obtain ⟨z, hzW, hz⟩ := hirr Wy hWy u v hu hv ⟨w, hwy, hwu⟩ ⟨y, hyW, hyv⟩
  exact ⟨z, trivial, hz⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : (X.homOfLE e ≫ U.ι) ⟨x, hx⟩ = V.ι ⟨x, hx⟩` using `by rw [X.homOfLE_ι]`. Simplify using `using h1`.
-/
theorem scheme_homOfLE_apply_mk {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (x : X) (hx : x ∈ V) :
    (X.homOfLE e) ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  apply Subtype.ext
  have h1 : (X.homOfLE e ≫ U.ι) ⟨x, hx⟩ = V.ι ⟨x, hx⟩ := by rw [X.homOfLE_ι]
  simpa using h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨y⟩ : Nonempty (Sp k)` from `inferInstance`. Conclude with `⟨y, Subsingleton.elim _ _⟩`.
-/
theorem surjective_spMap_of_field {F k : Type} [Field F] [Field k] (f : F →+* k) :
    Surjective (spMap f) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (Sp k) := inferInstance
  exact ⟨y, Subsingleton.elim _ _⟩

/- English proof (translation)
Introduce `F _ X h k _ f U hU hV`. Use `haveI := surjective_spMap_of_field f`. Use `set q := pullback.fst (U.ι ≫ h) (spMap f) with hq`. Establish `hqs : Function.Surjective q` using `q.surjective`. Establish `key : ∀ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) → IsOpen (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧ IsPreirreducible (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧ ∀ p, U.ι (q p) ∈ V → p ∈ Set.range (pullback.snd (X.homOfLE hVU) q)`.

Introduce `V hVU hirrV`. Use `⟨(pullback.snd (X.homOfLE hVU) q).isOpenEmbedding.isOpen_range, ?_, ?_⟩` and prove the remaining obligations. Set `e : pullback (V.ι ≫ h) (spMap f) ≅ pullback (X.homOfLE hVU) q` to `pullback.congrHom (by rw [← X.homOfLE_ι hVU, Category.assoc]) rfl ≪≫ (pullbackRightPullbackFstIso (U.ι ≫ h) (spMap f) (X.homOfLE hVU)).symm haveI : IrreducibleSpace ↑(pullback (X.homOfLE hVU) q) := (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous`. Rewrite using `[← Set.image_univ]`. Conclude with `(PreirreducibleSpace.isPreirreducible_univ (X := ↑(pullback (X.homOfLE hVU) q))).image _ (pullback.snd (X.homOfLE hVU) q).continuous.continuousOn`.

Introduce `p hp`. Rewrite using `[Scheme.Pullback.range_snd]`. Use `⟨⟨U.ι (q p), hp⟩, ?_⟩` and prove the remaining obligations. Use `show (X.homOfLE hVU) ⟨U.ι (q p), hp⟩ = q p`. Rewrite using `[scheme_homOfLE_apply_mk]`.

Both sides reduce to the same expression. Establish `hUne : (U : Set X).Nonempty` using `hU.nonempty`. Take `⟨y₀, hy₀⟩` from `hUne`. Take `⟨p₀, -⟩` from `hqs ⟨y₀, hy₀⟩`. Use `haveI : Nonempty ↑(pullback (U.ι ≫ h) (spMap f)) := ⟨p₀⟩`.

Set `S : Set (Set ↑(pullback (U.ι ≫ h) (spMap f)))` to `{W | ∃ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) ∧ (V : Set X).Nonempty ∧ W = Set.range (pullback.snd (X.homOfLE hVU) q)}`. Use `irreducibleSpace_of_open_cover_meeting S ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `W ⟨V, hVU, hi, -, rfl⟩`. Conclude with `(key V hVU hi).1`. Introduce and unpack `W ⟨V, hVU, hi, -, rfl⟩`.

Conclude with `(key V hVU hi).2.1`. Introduce `p`. Establish `hyU : U.ι (q p) ∈ U` using `(q p).2`. Take `⟨V, hVU, hyV, hi⟩` from `hV _ hyU`. Conclude with `⟨_, ⟨V, hVU, hi, ⟨_, hyV⟩, rfl⟩, (key V hVU hi).2.2 p hyV⟩`.

Introduce and unpack `W ⟨V, hVU, hi, ⟨a, ha⟩, rfl⟩ W' ⟨V', hVU', hi', ⟨b, hb⟩, rfl⟩`. Take `⟨z, hzU, hzV, hzV'⟩` from `hU.2 (V : Set X) (V' : Set X) V.isOpen V'.isOpen ⟨a, hVU ha, ha⟩ ⟨b, hVU' hb, hb⟩`. Take `⟨p, hp⟩` from `hqs ⟨z, hzU⟩`. Establish `hpz : U.ι (q p) = z` using `by rw [hp]; rfl`. Conclude with `⟨p, (key V hVU hi).2.2 p (hpz ▸ hzV), (key V' hVU' hi').2.2 p (hpz ▸ hzV')⟩`.
-/
theorem irreducibleSpace_pullback_of_cover : ∀ {F : Type} [Field F] {X : Scheme.{0}} (h : X ⟶ Sp F) (k : Type)
    [Field k] (f : F →+* k) (U : X.Opens),
    IsIrreducible (U : Set X) →
    (∀ y ∈ U, ∃ V : X.Opens, V ≤ U ∧ y ∈ V ∧ IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f))) →
    IrreducibleSpace ↑(pullback (U.ι ≫ h) (spMap f)) := by
  intro F _ X h k _ f U hU hV
  haveI := surjective_spMap_of_field f
  set q := pullback.fst (U.ι ≫ h) (spMap f) with hq
  have hqs : Function.Surjective q := q.surjective

  have key : ∀ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) →
      IsOpen (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      IsPreirreducible (Set.range (pullback.snd (X.homOfLE hVU) q)) ∧
      ∀ p, U.ι (q p) ∈ V → p ∈ Set.range (pullback.snd (X.homOfLE hVU) q) := by
    intro V hVU hirrV
    refine ⟨(pullback.snd (X.homOfLE hVU) q).isOpenEmbedding.isOpen_range, ?_, ?_⟩
    · let e : pullback (V.ι ≫ h) (spMap f) ≅ pullback (X.homOfLE hVU) q :=
        pullback.congrHom (by rw [← X.homOfLE_ι hVU, Category.assoc]) rfl ≪≫
          (pullbackRightPullbackFstIso (U.ι ≫ h) (spMap f) (X.homOfLE hVU)).symm
      haveI : IrreducibleSpace ↑(pullback (X.homOfLE hVU) q) :=
        (Scheme.homeoOfIso e).surjective.irreducibleSpace (Scheme.homeoOfIso e).continuous
      rw [← Set.image_univ]
      exact (PreirreducibleSpace.isPreirreducible_univ (X := ↑(pullback (X.homOfLE hVU) q))).image _
        (pullback.snd (X.homOfLE hVU) q).continuous.continuousOn
    · intro p hp
      rw [Scheme.Pullback.range_snd]
      refine ⟨⟨U.ι (q p), hp⟩, ?_⟩
      show (X.homOfLE hVU) ⟨U.ι (q p), hp⟩ = q p
      rw [scheme_homOfLE_apply_mk]
      rfl
  have hUne : (U : Set X).Nonempty := hU.nonempty
  obtain ⟨y₀, hy₀⟩ := hUne
  obtain ⟨p₀, -⟩ := hqs ⟨y₀, hy₀⟩
  haveI : Nonempty ↑(pullback (U.ι ≫ h) (spMap f)) := ⟨p₀⟩
  let S : Set (Set ↑(pullback (U.ι ≫ h) (spMap f))) :=
    {W | ∃ (V : X.Opens) (hVU : V ≤ U), IrreducibleSpace ↑(pullback (V.ι ≫ h) (spMap f)) ∧
      (V : Set X).Nonempty ∧ W = Set.range (pullback.snd (X.homOfLE hVU) q)}
  refine irreducibleSpace_of_open_cover_meeting S ?_ ?_ ?_ ?_
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).1
  · rintro W ⟨V, hVU, hi, -, rfl⟩
    exact (key V hVU hi).2.1
  · intro p
    have hyU : U.ι (q p) ∈ U := (q p).2
    obtain ⟨V, hVU, hyV, hi⟩ := hV _ hyU
    exact ⟨_, ⟨V, hVU, hi, ⟨_, hyV⟩, rfl⟩, (key V hVU hi).2.2 p hyV⟩
  · rintro W ⟨V, hVU, hi, ⟨a, ha⟩, rfl⟩ W' ⟨V', hVU', hi', ⟨b, hb⟩, rfl⟩
    obtain ⟨z, hzU, hzV, hzV'⟩ :=
      hU.2 (V : Set X) (V' : Set X) V.isOpen V'.isOpen ⟨a, hVU ha, ha⟩ ⟨b, hVU' hb, hb⟩
    obtain ⟨p, hp⟩ := hqs ⟨z, hzU⟩
    have hpz : U.ι (q p) = z := by rw [hp]; rfl
    exact ⟨p, (key V hVU hi).2.2 p (hpz ▸ hzV), (key V' hVU' hi').2.2 p (hpz ▸ hzV')⟩

end GlobalTheory
