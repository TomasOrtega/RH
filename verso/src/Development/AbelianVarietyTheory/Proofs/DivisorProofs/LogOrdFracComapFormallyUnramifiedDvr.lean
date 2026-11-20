import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrictOrd

open IsLocalRing

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `ha`. Establish `hb' : ((b : V) : L) = φ (a : K)`. Rewrite using `[hb]`. Both sides reduce to the same expression.

Establish `ha0 : (a : K) ≠ 0`. Introduce `h0`. Establish `: ((b : V) : L) = 0` using `by rw [hb', h0, map_zero]`. Conclude with `b.ne_zero (Subtype.ext this)`. Establish `hmem : (a : K)⁻¹ ∈ V.comap φ`.

Express the relevant statement in the definitionally equal form `φ (a : K)⁻¹ ∈ V`. Rewrite using `[map_inv₀, ← hb']`. Establish `: ((b⁻¹ : Vˣ) : V) * (b : V) = 1` using `b.inv_mul`. Establish `h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹`. Conclude with `eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)`.

Rewrite using `[← h2]`. Conclude with `((b⁻¹ : Vˣ) : V).2`. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩`.
-/
theorem isLocalHom_restrict {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) :
    IsLocalHom (φ.restrict (V.comap φ) V fun _ hx => hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha
  have hb' : ((b : V) : L) = φ (a : K) := by
    rw [hb]; rfl
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((b : V) : L) = 0 := by rw [hb', h0, map_zero]
    exact b.ne_zero (Subtype.ext this)
  have hmem : (a : K)⁻¹ ∈ V.comap φ := by
    change φ (a : K)⁻¹ ∈ V
    rw [map_inv₀, ← hb']
    have : ((b⁻¹ : Vˣ) : V) * (b : V) = 1 := b.inv_mul
    have h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
    rw [← h2]
    exact ((b⁻¹ : Vˣ) : V).2
  exact isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/- English proof (translation)
Introduce `h g hg`. Use `set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef`. Use `letI := ψ.toAlgebra`. Take `⟨hu, he⟩` from `h`. Use `haveI : IsLocalHom ψ := isLocalHom_restrict φ V`.

Use `haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)`. Establish `hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V` using `Algebra.FormallyUnramified.map_maximalIdeal`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible (V.comap φ)`. Establish `ht' : Irreducible (ψ t)`. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span, Set.image_singleton]`.

Both sides reduce to the same expression. Conclude with `GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg`.
-/
theorem log_ordFrac_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)] :
    (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra;
      Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) →
    ∀ g : K, g ≠ 0 →
      WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  intro h g hg
  set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef
  letI := ψ.toAlgebra
  obtain ⟨hu, he⟩ := h
  haveI : IsLocalHom ψ := isLocalHom_restrict φ V
  haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)
  have hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have ht' : Irreducible (ψ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg

end GlobalTheory.RestrictOrd
