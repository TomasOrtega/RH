import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish `h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s)`. Introduce `r hr`. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)`. Rewrite using `[h p hp, h q hq]`.
-/
theorem genMap_germ_eq_genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) := by
  have h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) =
      (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)
  rw [h p hp, h q hq]

/- English proof (translation)
Take `⟨g, rfl⟩` from `ha`. Take `⟨U, hU, s, rfl⟩` from `X.presheaf.exists_germ_eq g`. Conclude with `⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩`.
-/
theorem exists_open_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  exact ⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩

/- English proof (translation)
Introduce `X Ω _ ξ p a`. Use `⟨exists_open_mem_regAt ξ p a, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨h0, h1, h2⟩`. Take `⟨U, hU, HU⟩` from `exists_open_mem_regAt ξ p a h1`. Take `⟨V, hV, HV⟩` from `exists_open_mem_regAt ξ p _ h2`.

Conclude with `⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩`.
-/
theorem regAt_unitAt_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), (a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) ∧ (unitAt ξ p a → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a) := by
  intro X Ω _ ξ p a
  refine ⟨exists_open_mem_regAt ξ p a, ?_⟩
  rintro ⟨h0, h1, h2⟩
  obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ p a h1
  obtain ⟨V, hV, HV⟩ := exists_open_mem_regAt ξ p _ h2
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩

end GlobalTheory.CompanionTheory.Ar
