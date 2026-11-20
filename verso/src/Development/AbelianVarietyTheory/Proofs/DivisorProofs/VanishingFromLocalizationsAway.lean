import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `B _ s hs b hb`. Assume the negation of the conclusion as `hne`. Set `I : Ideal B` to `LinearMap.ker (LinearMap.toSpanSingleton B B b)`. Establish `hI : I ≠ ⊤`. Introduce `h`.

Establish `h1 : (1 : B) ∈ I` using `h ▸ Submodule.mem_top`. Establish `: (1 : B) • b = 0` using `h1`. Conclude with `hne (by simpa using this)`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨f, hfs, hfM⟩` from `hs ⟨M, hM.isPrime⟩`.

Establish `h0` using `hb f hfs`. Rewrite `h0` using `[IsLocalization.map_eq_zero_iff (Submonoid.powers f)]`. Take `⟨⟨m, n, rfl⟩, hm⟩` from `h0`. Establish `hmI : f ^ n ∈ I` using `by show (f ^ n) • b = 0`. Simplify using `using hm`.

Conclude with `hfM (hM.isPrime.mem_of_pow_mem n (hIM hmI))`.
-/
theorem GlobalTheory.PDiv.eq_zero_of_away_eq_zero_of_forall_prime :
    ∀ (B : Type) [CommRing B] (s : Set B), (∀ P : PrimeSpectrum B, ∃ f ∈ s, f ∉ P.asIdeal) → ∀ b : B, (∀ f ∈ s, algebraMap B (Localization.Away f) b = 0) → b = 0 := by
  intro B _ s hs b hb
  by_contra hne
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    have : (1 : B) • b = 0 := h1
    exact hne (by simpa using this)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨f, hfs, hfM⟩ := hs ⟨M, hM.isPrime⟩
  have h0 := hb f hfs
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at h0
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := h0
  have hmI : f ^ n ∈ I := by
    show (f ^ n) • b = 0
    simpa using hm
  exact hfM (hM.isPrime.mem_of_pow_mem n (hIM hmI))
