import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

/- English proof (translation)
Take `⟨x, hfx⟩` from `hx`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Use `haveI : Nonempty U := ⟨⟨x, hx⟩⟩`. Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (hU.fromSpec ≫ p)`.

Establish `key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal`. Introduce `q`. Establish `h : p (hU.fromSpec q) = (Spec.map φ) q`. Rewrite using `[hφ]`. Both sides reduce to the same expression.

Rewrite using `[h]`. Both sides reduce to the same expression. Establish `key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal`. Introduce `y`. Rewrite using `[← key, hU.fromSpec_primeIdealOf]`.

Establish `ha : φ.hom f ≠ 0`. Introduce `h0`. Establish `hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S))` using `(PrimeSpectrum.basicOpen f).isOpen`. Establish `hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty` using `⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩`. Take `⟨y, hy⟩` from `p.denseRange.exists_mem_open hO hne`.

Take `⟨w, hwU, hw⟩` from `nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩`. Establish `: f ∈ (p w).asIdeal` using `(key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)`. Conclude with `hw this`. Establish `hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal` using `(Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)`. Take `⟨Q, hQ, -⟩` from `Ideal.exists_minimalPrimes_le hle`.

Use `haveI hQp : Q.IsPrime := hQ.1.1`. Establish `haQ : φ.hom f ∈ Q` using `hQ.1.2 (Ideal.mem_span_singleton_self _)`. Establish `h1 : Q.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ`. Establish `h0 : Q.height ≠ 0`. Introduce `h`.

Rewrite `h` using `[Ideal.height_eq_zero_iff_eq_bot]`. Conclude with `ha (by simpa [h] using haQ)`. Establish `hQ1 : Q.height = 1` using `le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)`. Set `P : PrimeSpectrum Γ(X, U)` to `⟨Q, hQp⟩`. Establish `hz : hU.fromSpec P ∈ U`.

Establish `: hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `z : U` to `⟨hU.fromSpec P, hz⟩`. Establish `hP : hU.primeIdealOf z = P` using `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)`. Use `clear_value z`.

Use `letI := X.presheaf.algebra_section_stalk z`. Use `haveI := hU.isLocalization_stalk z`. Use `⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩` and prove the remaining obligations. Use `IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal (X.presheaf.stalk (z : X))` as an intermediate fact. Rewrite using `[this, hP]`.

Express the relevant statement in the definitionally equal form `((Q.height : ℕ∞) : WithBot ℕ∞) = 1`. Rewrite using `[hQ1]`. Both sides reduce to the same expression.
-/
theorem exists_vert_of_mem (S : Type) [CommRing S] [IsDomain S] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp S) [IsDominant p] (f : S) (hf : f ≠ 0) (hx : ∃ x : X, f ∈ (p x).asIdeal) : ∃ z : X, Vert p f z := by
  obtain ⟨x, hfx⟩ := hx
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  have key : ∀ q : PrimeSpectrum Γ(X, U), f ∈ (p (hU.fromSpec q)).asIdeal ↔ φ.hom f ∈ q.asIdeal := by
    intro q
    have h : p (hU.fromSpec q) = (Spec.map φ) q := by
      rw [hφ]; rfl
    rw [h]; rfl
  have key' : ∀ y : U, f ∈ (p y.1).asIdeal ↔ φ.hom f ∈ (hU.primeIdealOf y).asIdeal := by
    intro y
    rw [← key, hU.fromSpec_primeIdealOf]
  have ha : φ.hom f ≠ 0 := by
    intro h0
    have hO : IsOpen ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) :=
      (PrimeSpectrum.basicOpen f).isOpen
    have hne : ((PrimeSpectrum.basicOpen f : TopologicalSpace.Opens (PrimeSpectrum S)) : Set (PrimeSpectrum S)).Nonempty :=
      ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩
    obtain ⟨y, hy⟩ := p.denseRange.exists_mem_open hO hne
    obtain ⟨w, hwU, hw⟩ := nonempty_preirreducible_inter U.isOpen (hO.preimage p.continuous) ⟨x, hx⟩ ⟨y, hy⟩
    have : f ∈ (p w).asIdeal := (key' ⟨w, hwU⟩).2 (h0 ▸ Ideal.zero_mem _)
    exact hw this
  have hle : Ideal.span {φ.hom f} ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ((key' ⟨x, hx⟩).1 hfx)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI hQp : Q.IsPrime := hQ.1.1
  have haQ : φ.hom f ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self _)
  have h1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have h0 : Q.height ≠ 0 := by
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    exact ha (by simpa [h] using haQ)
  have hQ1 : Q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h0)
  let P : PrimeSpectrum Γ(X, U) := ⟨Q, hQp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  clear_value z
  letI := X.presheaf.algebra_section_stalk z
  haveI := hU.isLocalization_stalk z
  refine ⟨z.1, ?_, (key' z).2 (by rw [hP]; exact haQ)⟩
  have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
    (X.presheaf.stalk (z : X))
  rw [this, hP]
  change ((Q.height : ℕ∞) : WithBot ℕ∞) = 1
  rw [hQ1]; rfl

end GlobalTheory.Desc
