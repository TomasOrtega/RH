import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap

/- English proof (translation)
Introduce `E _ _ Ω Vs K C _ _ _ _ _ ρ R' g ℓ ψ j ρK ρC hρ hK hC a x`. Establish `hex : ∀ i, ∃ c : Fin g → R', ρ a (ℓ i) = comb ℓ c`. Introduce `i`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R').1 (hρ a i)`. Conclude with `⟨c, by rw [← hc]; rfl⟩`.

Use `choose c hc using hex`. Establish `hs : ∀ i, comb ℓ (Pi.single i (1 : R') : Fin g → R') = ℓ i`. Introduce `i`. Unfold `comb`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ i, ρK a (Pi.single i (1 : K)) = fun k => ψ (c i k)`.

Introduce `i`. Use `hK a (Pi.single i 1) (c i) (by rw [hs, hc])` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use extensionality with `k`.

Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Establish `h2 : ∀ i, ρC a (Pi.single i (1 : C)) = fun k => j (ψ (c i k))`.

Introduce `i`. Use `hC a (Pi.single i 1) (c i) (by rw [hs, hc])` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[← this]`. Use `congr 1`.

Use extensionality with `k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.

Establish `hxK : x = ∑ i, x i • (Pi.single i (1 : K) : Fin g → K)`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hxC : (fun i => j (x i)) = ∑ i, j (x i) • (Pi.single i (1 : C) : Fin g → C)`. Use extensionality with `k`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hxC, map_sum]`. Use `conv_rhs => rw [hxK, map_sum]`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, h1, h2]`.
-/
theorem tied_map_comp : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  intro E _ _ Ω Vs K C _ _ _ _ _ ρ R' g ℓ ψ j ρK ρC hρ hK hC a x
  have hex : ∀ i, ∃ c : Fin g → R', ρ a (ℓ i) = comb ℓ c := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 (hρ a i)
    exact ⟨c, by rw [← hc]; rfl⟩
  choose c hc using hex
  have hs : ∀ i, comb ℓ (Pi.single i (1 : R') : Fin g → R') = ℓ i := by
    intro i
    unfold comb
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have h1 : ∀ i, ρK a (Pi.single i (1 : K)) = fun k => ψ (c i k) := by
    intro i
    have := hK a (Pi.single i 1) (c i) (by rw [hs, hc])
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h2 : ∀ i, ρC a (Pi.single i (1 : C)) = fun k => j (ψ (c i k)) := by
    intro i
    have := hC a (Pi.single i 1) (c i) (by rw [hs, hc])
    simp only [RingHom.comp_apply] at this
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hxK : x = ∑ i, x i • (Pi.single i (1 : K) : Fin g → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hxC : (fun i => j (x i)) = ∑ i, j (x i) • (Pi.single i (1 : C) : Fin g → C) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hxC, map_sum]
  conv_rhs => rw [hxK, map_sum]
  ext k
  simp [Finset.sum_apply, h1, h2]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap
