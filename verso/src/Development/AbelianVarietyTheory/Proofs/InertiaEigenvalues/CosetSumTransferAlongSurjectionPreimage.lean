import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

namespace GlobalTheory

/- English proof (translation)
Use `set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF`. Set `t : H ⧸ K → T` to `fun d => (hψ d.out).choose`. Establish `ht : ∀ d, ψ (t d) = d.out` using `fun d => (hψ d.out).choose_spec`. Set `f : H ⧸ K → G ⧸ U0` to `fun d => ((t d : G) : G ⧸ U0)`. Establish `key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) → ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k`.

Introduce `x y hxy`. Rewrite `hxy` using `[QuotientGroup.eq]`. Use `⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩` and prove the remaining obligations. Simplify using `[map_mul, map_inv]`. Establish `hinj : Function.Injective f`.

Introduce `d d' h`. Take `⟨-, k, hk, hkk⟩` from `key _ _ h`. Rewrite `hkk` using `[ht, ht]`. Rewrite using `[← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]`. Simplify using `using hk`.

Establish `hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧ a (((ψ x : H) : H ⧸ K).out) = a (ψ x)`. Introduce `x`. Use `set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd`. Establish `h1 : d.out⁻¹ * ψ x ∈ K`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)`. Rewrite using `[QuotientGroup.eq]`. Establish `: ψ ((t d)⁻¹ * x) ∈ K` using `by simpa [map_mul, map_inv, ht] using h1`. Simplify using `using (hTU _).1 this`.

Use `ha d.out _ h1` as an intermediate fact. Simplify using `using this.symm`. Establish `hval : ∀ d, F (f d) = a d.out • β (t d)`. Introduce `d`. Establish `hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T` using `⟨t d, rfl, (t d).2⟩`.

Simplify using `only [hF, dif_pos hc]`. Take `⟨hU, k, hk, hkk⟩` from `key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm`. Rewrite using `[hkk, ha _ k hk, ht]`. Use `congr 1`. Use `hβ (t d : G) _ hU` as an intermediate fact.

Simplify using `using this`. Use `set S : Finset (H ⧸ K) := hfin.toFinset with hS`. Establish `hsupp : Function.support F ⊆ ↑(S.image f)`. Introduce `c hc`. Rewrite `hc` using `[Function.mem_support]`.

Establish `hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T`. Assume the negation of the conclusion as `hn`. Conclude with `hc (by simp only [hF, dif_neg hn])`. Take `⟨x, rfl, hx⟩` from `hc'`. Take `⟨h1, h2⟩` from `hcover ⟨x, hx⟩`.

Use `Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)` and prove the remaining obligations. Rewrite using `[hS, Set.Finite.mem_toFinset, Function.mem_support, h2]`. Introduce `h0`. Apply `hc` to reduce the goal to its premises. Establish `hF'` using `hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)`.

Rewrite `hF'` using `[h1, h2, h0, zero_smul]`. Conclude with `hF'`. Establish `hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S`. Introduce `d hd`. Rewrite using `[hS, Set.Finite.coe_toFinset]`.

Conclude with `fun h0 => hd (by simp only [h0, zero_mul])`. Rewrite using `[finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hval, map_smul, smul_eq_mul, ← hφ, ht]`.
-/
theorem cosetSum_transfer_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H)
    (hψ : Function.Surjective ψ) (hTU : ∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0)
    (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ)
    (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x)
    (hfin : (Function.support fun d : H ⧸ K => a d.out).Finite)
    (hβ : ∀ x, ∀ u ∈ U0, β (x * u) = β x)
    (hφ : ∀ t : T, φ' (ψ t) = lam (β t)) :
    ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0,
      if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  classical
  set F : G ⧸ U0 → V := fun c => if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then
        a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0 with hF
  let t : H ⧸ K → T := fun d => (hψ d.out).choose
  have ht : ∀ d, ψ (t d) = d.out := fun d => (hψ d.out).choose_spec
  let f : H ⧸ K → G ⧸ U0 := fun d => ((t d : G) : G ⧸ U0)

  have key : ∀ x y : T, ((x : G) : G ⧸ U0) = ((y : G) : G ⧸ U0) →
      ((x : G)⁻¹ * y ∈ U0) ∧ ∃ k ∈ K, ψ y = ψ x * k := by
    intro x y hxy
    rw [QuotientGroup.eq] at hxy
    refine ⟨hxy, ψ (x⁻¹ * y), (hTU _).2 (by simpa using hxy), ?_⟩
    simp [map_mul, map_inv]

  have hinj : Function.Injective f := by
    intro d d' h
    obtain ⟨-, k, hk, hkk⟩ := key _ _ h
    rw [ht, ht] at hkk
    rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d', QuotientGroup.eq, hkk]
    simpa using hk

  have hcover : ∀ x : T, f ((ψ x : H) : H ⧸ K) = ((x : G) : G ⧸ U0) ∧
      a (((ψ x : H) : H ⧸ K).out) = a (ψ x) := by
    intro x
    set d : H ⧸ K := ((ψ x : H) : H ⧸ K) with hd
    have h1 : d.out⁻¹ * ψ x ∈ K := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · show (((t d : T) : G) : G ⧸ U0) = ((x : G) : G ⧸ U0)
      rw [QuotientGroup.eq]
      have : ψ ((t d)⁻¹ * x) ∈ K := by simpa [map_mul, map_inv, ht] using h1
      simpa using (hTU _).1 this
    · have := ha d.out _ h1
      simpa using this.symm

  have hval : ∀ d, F (f d) = a d.out • β (t d) := by
    intro d
    have hc : ∃ x : G, (x : G ⧸ U0) = f d ∧ x ∈ T := ⟨t d, rfl, (t d).2⟩
    simp only [hF, dif_pos hc]
    obtain ⟨hU, k, hk, hkk⟩ := key (t d) ⟨hc.choose, hc.choose_spec.2⟩ hc.choose_spec.1.symm
    rw [hkk, ha _ k hk, ht]
    congr 1
    have := hβ (t d : G) _ hU
    simpa using this

  set S : Finset (H ⧸ K) := hfin.toFinset with hS
  have hsupp : Function.support F ⊆ ↑(S.image f) := by
    intro c hc
    rw [Function.mem_support] at hc
    have hc' : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T := by
      by_contra hn
      exact hc (by simp only [hF, dif_neg hn])
    obtain ⟨x, rfl, hx⟩ := hc'
    obtain ⟨h1, h2⟩ := hcover ⟨x, hx⟩
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, ?_, h1⟩)
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support, h2]
    intro h0
    apply hc
    have hF' := hval ((ψ ⟨x, hx⟩ : H) : H ⧸ K)
    rw [h1, h2, h0, zero_smul] at hF'
    exact hF'
  have hL : Function.support (fun d : H ⧸ K => a d.out * φ' d.out) ⊆ ↑S := by
    intro d hd
    rw [hS, Set.Finite.coe_toFinset]
    exact fun h0 => hd (by simp only [h0, zero_mul])
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_image (fun d _ d' _ h => hinj h), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hval, map_smul, smul_eq_mul, ← hφ, ht]

end GlobalTheory
