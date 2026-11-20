import Mathlib
open AlgebraicGeometry CategoryTheory Limits Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `X T p W U V hU hV e hW b hb q`. Use `set f := hU.fromSpec with hf`. Establish `hemb : IsOpenEmbedding f` using `f.isOpenEmbedding`. Establish `hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U` using `fun P => hU.range_fromSpec.le ⟨P, rfl⟩`. Establish `hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P` using `fun P => hemb.injective (hU.fromSpec_primeIdealOf _)`.

Establish `hcomap : ∀ P : PrimeSpectrum Γ(X, U), PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩`. Introduce `P`. Use `IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)` as an intermediate fact. Rewrite `this` using `[hprime P]`. Conclude with `this`.

Use `set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA`. Establish `hq : q ∈ closure (f ⁻¹' A)`. Rewrite using `[← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]`. Conclude with `hW (f q)`. Use `closure_mono ?_ hq` and prove the remaining obligations.

Introduce `P hP`. Take `⟨hPW, hPp⟩` from `hP`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `_ : Algebra Γ(X, U) (X.presheaf.stalk (f P))` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩ haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)`. Establish `h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0` using `hb (f P) (hmemU P) hPW`.

Take `⟨⟨s, hs⟩, hsb⟩` from `(IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0`. Conclude with `⟨s, hs, hsb⟩`. Use `show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q`. Rewrite using `[hcomap P, hcomap q]`. Establish `: p (f P) = p (f q)` using `hPp`.

Use `congr 2`.
-/
theorem fibre_dense_affine_chart_primes : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  intro X T p W U V hU hV e hW b hb q
  set f := hU.fromSpec with hf
  have hemb : IsOpenEmbedding f := f.isOpenEmbedding

  have hmemU : ∀ P : PrimeSpectrum Γ(X, U), f P ∈ U := fun P => hU.range_fromSpec.le ⟨P, rfl⟩
  have hprime : ∀ P : PrimeSpectrum Γ(X, U), hU.primeIdealOf ⟨f P, hmemU P⟩ = P := fun P =>
    hemb.injective (hU.fromSpec_primeIdealOf _)
  have hcomap : ∀ P : PrimeSpectrum Γ(X, U),
      PrimeSpectrum.comap (p.appLE V U e).hom P = hV.primeIdealOf ⟨p (f P), e (hmemU P)⟩ := by
    intro P
    have := IsAffineOpen.comap_primeIdealOf_appLE (f := p) V hV U hU e (hmemU P)
    rw [hprime P] at this
    exact this
  set A : Set X := (W : Set X) ∩ p ⁻¹' {p (f q)} with hA
  have hq : q ∈ closure (f ⁻¹' A) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hW (f q)
  refine closure_mono ?_ hq
  intro P hP
  obtain ⟨hPW, hPp⟩ := hP
  refine ⟨?_, ?_⟩
  · let _ : Algebra Γ(X, U) (X.presheaf.stalk (f P)) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f P, hmemU P⟩
    haveI hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (f P)) := hU.isLocalization_stalk' P (hmemU P)
    have h0 : algebraMap Γ(X, U) (X.presheaf.stalk (f P)) b = 0 := hb (f P) (hmemU P) hPW
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff P.asIdeal.primeCompl _ b).mp h0
    exact ⟨s, hs, hsb⟩
  · show PrimeSpectrum.comap (p.appLE V U e).hom P = PrimeSpectrum.comap (p.appLE V U e).hom q
    rw [hcomap P, hcomap q]
    have : p (f P) = p (f q) := hPp
    congr 2

end GlobalTheory
