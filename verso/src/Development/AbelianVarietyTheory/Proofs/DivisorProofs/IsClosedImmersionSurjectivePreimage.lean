import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.GlueColim

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `B₀ 𝒰 F _ _ X G hG hc e he hs hnat j hj`. Establish `hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : (G U.1).toScheme), F.map f (e U x) = e V (X.homOfLE (hG (show U.1 ≤ V.1 from f.le)) x)`. Introduce `U V f x`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat (show U.1 ≤ V.1 from f.le)]`. Both sides reduce to the same expression.

Establish `hinj : ∀ U, Function.Injective (e U)` using `fun U ↦ (e U).isClosedEmbedding.injective`. Establish `key2 : ∀ {U V : 𝒰} (x : (G U.1).toScheme) (y : (G V.1).toScheme), colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1`. Introduce `U V x y h`. Take `⟨W, f, g, z, h1, h2⟩` from `(Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h`. Take `⟨z, rfl⟩` from `(e W).surjective z`.

Rewrite `h1`, `h2` using `[hnat']`. Establish `h1'` using `congrArg Subtype.val (hinj _ h1)`. Establish `h2'` using `congrArg Subtype.val (hinj _ h2)`. Simplify using `only [Scheme.homOfLE_apply] at h1' h2'`. Conclude with `h1'.symm.trans h2'`.

Establish `hj' : ∀ (U : 𝒰) (x : (G U.1).toScheme), j x.1 = colimit.ι F U (e U x)` using `fun U x ↦ congr($(hj U) x)`. Establish `hpre : ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1`. Introduce `U`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy⟩`. Take `⟨y, rfl⟩` from `(e U).surjective y`. Take `⟨V, hV, hxV⟩` from `hc x`. Use `key2 (V := ⟨V, hV⟩) y ⟨x, hxV⟩ (hy.trans (hj' ⟨V, hV⟩ ⟨x, hxV⟩))` as an intermediate fact. Establish `h2 : y.1 = x` using `this`.

Conclude with `h2 ▸ y.2`. Introduce `hx`. Conclude with `⟨_, (hj' U ⟨x, hx⟩).symm⟩`. Use `⟨?_, ⟨?_⟩, hpre⟩` and prove the remaining obligations. Rewrite using `[IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) (Scheme.IsLocallyDirected.openCover F)]`.

Introduce `U`. Establish `H : IsPullback (e U) (G U.1).ι (colimit.ι F U) j` using `IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)`. Establish `: pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U` using `by simp`. Express the relevant statement in the definitionally equal form `IsClosedImmersion (pullback.snd j (colimit.ι F U))`. Rewrite using `[this]`.

Use `infer_instance`. Introduce `b`. Take `⟨U, x, rfl⟩` from `Scheme.IsLocallyDirected.ι_jointly_surjective F b`. Take `⟨x, rfl⟩` from `(e U).surjective x`. Conclude with `⟨_, hj' U x⟩`.
-/
theorem isClosedImmersion_surjective_preimage : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  intro B₀ 𝒰 F _ _ X G hG hc e he hs hnat j hj
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : (G U.1).toScheme),
      F.map f (e U x) = e V (X.homOfLE (hG (show U.1 ≤ V.1 from f.le)) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat (show U.1 ≤ V.1 from f.le)]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key2 : ∀ {U V : 𝒰} (x : (G U.1).toScheme) (y : (G V.1).toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hj' : ∀ (U : 𝒰) (x : (G U.1).toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV, hxV⟩ := hc x
      have := key2 (V := ⟨V, hV⟩) y ⟨x, hxV⟩ (hy.trans (hj' ⟨V, hV⟩ ⟨x, hxV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨?_, ⟨?_⟩, hpre⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) (G U.1).ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩

end GlobalTheory.GlueColim
