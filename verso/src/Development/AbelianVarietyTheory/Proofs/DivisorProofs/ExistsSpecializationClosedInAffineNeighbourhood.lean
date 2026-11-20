import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedPt

/- English proof (translation)
Take `⟨N, hN, hle⟩` from `Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top`. Use `⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩` and prove the remaining obligations. Establish `h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V))` using `(PrimeSpectrum.le_iff_specializes _ _).mp hle`. Establish `h2` using `Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous`. Rewrite `h2` using `[hV.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.
-/
lemma exists_max_specializes {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (x : Y)
    (hx : x ∈ V) : ∃ N : PrimeSpectrum Γ(Y, V), N.asIdeal.IsMaximal ∧
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ N.asIdeal ∧ x ⤳ hV.fromSpec N := by
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
  refine ⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩
  have h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous
  rwa [hV.fromSpec_primeIdealOf] at h2

/- English proof (translation)
Establish `: hV.fromSpec N ∈ Set.range hV.fromSpec` using `⟨N, rfl⟩`. Rewrite `this` using `[hV.range_fromSpec]`. Then use the resulting hypothesis.
-/
lemma fromSpec_mem {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    (N : PrimeSpectrum Γ(Y, V)) : hV.fromSpec N ∈ V := by
  have : hV.fromSpec N ∈ Set.range hV.fromSpec := ⟨N, rfl⟩
  rwa [hV.range_fromSpec] at this

/- English proof (translation)
Introduce `Y x`. Take `⟨V, hV, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial`. Take `⟨N, hN, -, hxN⟩` from `exists_max_specializes hV x hx`. Use `⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩` and prove the remaining obligations. Introduce `V₂ hle hV₂ hy`.

Establish `hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N`. Introduce `y₁ hy₁ hs`. Establish `e` using `hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩`. Establish `hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩)`. Rewrite using `[e]`.

Conclude with `hs`. Establish `h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩` using `(hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'`. Establish `h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩` using `(PrimeSpectrum.le_iff_specializes _ _).mpr h3`. Establish `h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩` using `PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)`. Rewrite using `[h5]`.

Conclude with `e.symm`. Use `⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩` and prove the remaining obligations. Take `⟨N₂, hN₂, -, hs⟩` from `exists_max_specializes hV₂ _ hy`. Establish `e` using `hcl _ (fromSpec_mem hV₂ N₂) hs`. Establish `e2` using `hV₂.fromSpec_primeIdealOf ⟨_, hy⟩`.

Establish `: N₂ = hV₂.primeIdealOf ⟨_, hy⟩` using `hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)`. Rewrite using `[← this]`. Conclude with `hN₂`. Introduce `a`. Establish `e2` using `hV₂.fromSpec_primeIdealOf ⟨_, hy⟩`.

Establish `h` using `hV₂.fromSpec_preimage_basicOpen a`. Establish `h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔ hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a`. Rewrite using `[← h]`. Both sides reduce to the same expression. Rewrite `h'` using `[e2, PrimeSpectrum.mem_basicOpen]`.

Conclude with `(not_iff_comm.mp h'.symm).symm`.
-/
theorem exists_closed_point : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  intro Y x
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial
  obtain ⟨N, hN, -, hxN⟩ := exists_max_specializes hV x hx
  refine ⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩
  intro V₂ hle hV₂ hy
  have hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N := by
    intro y₁ hy₁ hs
    have e := hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩
    have hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩) := by
      rw [e]; exact hs
    have h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'
    have h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩ := (PrimeSpectrum.le_iff_specializes _ _).mpr h3
    have h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)
    rw [h5]; exact e.symm
  refine ⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩
  · obtain ⟨N₂, hN₂, -, hs⟩ := exists_max_specializes hV₂ _ hy
    have e := hcl _ (fromSpec_mem hV₂ N₂) hs
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have : N₂ = hV₂.primeIdealOf ⟨_, hy⟩ :=
      hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)
    rw [← this]; exact hN₂
  · intro a
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have h := hV₂.fromSpec_preimage_basicOpen a
    have h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔
        hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a := by
      rw [← h]; rfl
    rw [e2, PrimeSpectrum.mem_basicOpen] at h'
    exact (not_iff_comm.mp h'.symm).symm

end GlobalTheory.ClosedPt
