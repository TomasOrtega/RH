import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `B₀ 𝒰 hbas F _hF e hinj hsurj hnat`. Establish `hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme), F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x)`. Introduce `U V f x`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]`. Both sides reduce to the same expression.

Establish `key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 → ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W), F.map f z = e U x ∧ F.map g z = e V y`. Introduce `U V x y h`. Take `⟨W, hW, hxW, h1, h2⟩` from `hbas U.1 U.2 V.1 V.2 x.1 x.2 (h ▸ y.2)`. Use `⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hnat']`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[hnat']`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h`. Prove the components needed by the constructor for the conclusion. Introduce `U V W f g x y h`. Take `⟨x, rfl⟩` from `hsurj U x`.

Take `⟨y, rfl⟩` from `hsurj V y`. Establish `h' : F.map f (e U x) = F.map g (e V y)` using `h`. Rewrite `h'` using `[hnat', hnat']`. Establish `h''` using `congrArg Subtype.val (hinj _ h')`. Conclude with `key x y (by simpa using h'')`.
-/
theorem isLocallyDirected_of_basis : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  intro B₀ 𝒰 hbas F _hF e hinj hsurj hnat
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  constructor
  intro U V W f g x y h
  obtain ⟨x, rfl⟩ := hsurj U x
  obtain ⟨y, rfl⟩ := hsurj V y
  have h' : F.map f (e U x) = F.map g (e V y) := h
  rw [hnat', hnat'] at h'
  have h'' := congrArg Subtype.val (hinj _ h')
  exact key x y (by simpa using h'')

end GlobalTheory.ThickGlue
