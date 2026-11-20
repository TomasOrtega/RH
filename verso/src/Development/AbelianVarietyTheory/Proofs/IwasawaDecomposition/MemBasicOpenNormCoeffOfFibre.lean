import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReversedCharpolyCoeffNotMemPrimeStatement
open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

/- English proof (translation)
Establish `hV'` using `hV.preimage f`. Establish `sq` using `hV.SpecMap_appLE_fromSpec f hV' le_rfl`. Rewrite `sq` using `[← Scheme.Hom.app_eq_appLE]`. Establish `pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q)` using `fun q => congr($(sq) q)`. Take `⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec` from `by rwa [hV.range_fromSpec]`.

Establish `e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal` using `fun c => by`. Rewrite using `[← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Establish `e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal` using `fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl`. Establish `inj` using `hV.fromSpec.isOpenEmbedding.injective`.

Establish `h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥`. Set `P0 : PrimeSpectrum Γ(X, V)` to `⟨⊥, Ideal.isPrime_bot⟩`. Take `⟨y, hy⟩` from `f.surjective (hV.fromSpec P0)`. Establish `hyV : f y ∈ V`. Establish `hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec` using `⟨P0, rfl⟩`.

Rewrite `hr` using `[hV.range_fromSpec]`. Rewrite using `[hy]`. Conclude with `hr`. Take `⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec` from `by rw [hV'.range_fromSpec]; exact hyV`. Conclude with `⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩`.

Take `⟨k, hk, hc⟩` from `GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime (fun Q hQ hQp => by`. Set `q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V)` to `⟨Q, hQ⟩`. Establish `e : PrimeSpectrum.comap (f.app V).hom q = p` using `PrimeSpectrum.ext hQp`. Conclude with `(e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))`. Conclude with `⟨k, hk, (e₁ _).2 hc⟩`.
-/
theorem mem_basicOpen_normCoeff_of_fibre {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    {V : X.Opens} (hV : IsAffineOpen V) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)]
    (τ : Γ(Y, f ⁻¹ᵁ V)) (x : X) (hx : x ∈ V) (h : ∀ y : Y, f y = x → y ∈ Y.basicOpen τ) :
    ∃ k, 1 ≤ k ∧ x ∈ X.basicOpen (normCoeff (f.app V).hom (f.finite_app V hV) τ k) := by
  have hV' := hV.preimage f
  have sq := hV.SpecMap_appLE_fromSpec f hV' le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at sq
  have pt : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V),
      hV.fromSpec (PrimeSpectrum.comap (f.app V).hom q) = f (hV'.fromSpec q) := fun q => congr($(sq) q)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have e₁ : ∀ c : Γ(X, V), hV.fromSpec p ∈ X.basicOpen c ↔ c ∉ p.asIdeal := fun c => by
    rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen]; rfl
  have e₂ : ∀ q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V), hV'.fromSpec q ∈ Y.basicOpen τ ↔ τ ∉ q.asIdeal :=
    fun q : Spec Γ(Y, f ⁻¹ᵁ V) => by rw [← Scheme.Hom.mem_preimage, hV'.fromSpec_preimage_basicOpen]; rfl
  have inj := hV.fromSpec.isOpenEmbedding.injective
  have h0 : ∃ Q : Ideal Γ(Y, f ⁻¹ᵁ V), Q.IsPrime ∧ Q.comap (f.app V).hom = ⊥ := by
    let P0 : PrimeSpectrum Γ(X, V) := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, hy⟩ := f.surjective (hV.fromSpec P0)
    have hyV : f y ∈ V := by
      have hr : hV.fromSpec P0 ∈ Set.range hV.fromSpec := ⟨P0, rfl⟩
      rw [hV.range_fromSpec] at hr
      rw [hy]; exact hr
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hyV
    exact ⟨q.asIdeal, q.isPrime, congrArg PrimeSpectrum.asIdeal (inj ((pt q).trans hy))⟩
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime (f.app V).hom (f.finite_app V hV) τ h0 p.asIdeal p.isPrime
    (fun Q hQ hQp => by
      let q : PrimeSpectrum Γ(Y, f ⁻¹ᵁ V) := ⟨Q, hQ⟩
      have e : PrimeSpectrum.comap (f.app V).hom q = p := PrimeSpectrum.ext hQp
      exact (e₂ q).1 (h _ ((pt q).symm.trans (congrArg hV.fromSpec e))))
  exact ⟨k, hk, (e₁ _).2 hc⟩

end GlobalTheory.NormalDescent
