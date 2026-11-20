import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLinearQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial

/- English proof (translation)
Introduce `F _ σ _ S hS`. Set `ℓ : (σ → F) →ₗ[F] MvPolynomial σ F` to `Fintype.linearCombination F (fun s => (X s : MvPolynomial σ F))`. Establish `hSrange : ∀ f ∈ S, f ∈ LinearMap.range ℓ`. Introduce `f hf`. Rewrite using `[Fintype.range_linearCombination, ← homogeneousSubmodule_one_eq_span_X]`.

Conclude with `hS f hf`. Set `L : Submodule F (σ → F)` to `(Submodule.span F S).comap ℓ`. Set `b` to `Module.finBasis F ((σ → F) ⧸ L)`. Set `r` to `Module.finrank F ((σ → F) ⧸ L)`. Set `θ : (σ → F) →ₗ[F] MvPolynomial (Fin r) F` to `Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) ∘ₗ (b.equivFun.toLinearMap ∘ₗ L.mkQ)`.

Establish `hθ : ∀ v, θ v = ∑ i, b.equivFun (L.mkQ v) i • (X i : MvPolynomial (Fin r) F)` using `fun v => rfl`. Set `φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F` to `aeval (fun s => θ (Pi.single s 1))`. Establish `key : ∀ c, φ (ℓ c) = θ c`. Establish `: φ.toLinearMap ∘ₗ ℓ = θ`. Use `LinearMap.pi_ext (fun s x => ?_)` and prove the remaining obligations.

Establish `hx : (Pi.single s x : σ → F) = x • Pi.single s (1 : F)`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`. Simplify using `only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ℓ, Fintype.linearCombination_apply_single, map_smul, φ, aeval_X]`. Rewrite using `[hx, map_smul]`. Conclude with `fun c => LinearMap.congr_fun this c`.

Set `lift : Fin r → (σ → F)` to `fun i => (L.mkQ_surjective (b i)).choose`. Establish `hlift : ∀ i, L.mkQ (lift i) = b i` using `fun i => (L.mkQ_surjective (b i)).choose_spec`. Set `ψ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial σ F` to `aeval (fun i => ℓ (lift i))`. Establish `hφψ : φ.comp ψ = AlgHom.id F _`. Use `MvPolynomial.algHom_ext (fun i => ?_)` and prove the remaining obligations.

Establish `he : b.equivFun (b i) = Pi.single i 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Module.Basis.equivFun_self, Pi.single_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Simplify using `only [AlgHom.comp_apply, ψ, aeval_X, key, AlgHom.id_apply]`. Rewrite using `[show θ (lift i) = Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) (b.equivFun (L.mkQ (lift i))) from rfl, hlift, he, Fintype.linearCombination_apply_single, one_smul]`. Establish `hψθ : ∀ v, ψ (θ v) = ℓ (∑ i, b.equivFun (L.mkQ v) i • lift i)`.

Introduce `v`. Rewrite using `[hθ, map_sum, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, aeval_X]`. Establish `hspan : Submodule.span F S ≤ (Ideal.span S).restrictScalars F` using `Submodule.span_le.mpr (fun f hf => Ideal.subset_span hf)`.

Use `⟨r, φ, fun p => ⟨ψ p, by simpa using AlgHom.congr_fun hφψ p⟩, ?_, fun s => ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises. Establish `hmk : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp (ψ.comp φ) = Ideal.Quotient.mkₐ F (Ideal.span S)`. Use `MvPolynomial.algHom_ext (fun s => ?_)` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`.

Rewrite using `[Ideal.Quotient.eq]`. Establish `h1 : φ (X s) = θ (Pi.single s 1)` using `aeval_X _ _`. Rewrite using `[h1, hψθ]`. Establish `hmem : (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) - Pi.single s 1 ∈ L`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]`.

Establish `: (Submodule.Quotient.mk (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) : (σ → F) ⧸ L) = ∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • b i`. Rewrite using `[← Submodule.mkQ_apply, map_sum]`. Simplify using `only [map_smul, hlift]`. Rewrite using `[this, b.sum_equivFun, Submodule.mkQ_apply, sub_self]`. Establish `h2` using `hspan hmem`.

Rewrite `h2` using `[map_sub]`. Establish `h3 : ℓ (Pi.single s 1) = X s`. Simplify using `[ℓ]`. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Introduce `f hf`.

Rewrite `hf` using `[RingHom.mem_ker]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Use `AlgHom.congr_fun hmk f` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this`. Rewrite using `[← this, hf, map_zero, map_zero]`.

Use `Ideal.span_le.mpr (fun f hf => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hSrange f hf`. Establish `hc : c ∈ L` using `Submodule.subset_span hf`. Use `show φ (ℓ c) = 0`. Rewrite using `[key, hθ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).mpr hc]`.

Simplify using the standard rewrite rules. Rewrite using `[← mem_homogeneousSubmodule, homogeneousSubmodule_one_eq_span_X, ← Fintype.range_linearCombination]`. Use `⟨b.equivFun (L.mkQ (Pi.single s 1)), ?_⟩` and prove the remaining obligations. Rewrite using `[show φ (X s) = θ (Pi.single s 1) from aeval_X _ _]`. Both sides reduce to the same expression.
-/
theorem LinearQuotient.proof : LinearQuotient.Statement := by
  intro F _ σ _ S hS
  classical

  let ℓ : (σ → F) →ₗ[F] MvPolynomial σ F := Fintype.linearCombination F (fun s => (X s : MvPolynomial σ F))
  have hSrange : ∀ f ∈ S, f ∈ LinearMap.range ℓ := by
    intro f hf
    rw [Fintype.range_linearCombination, ← homogeneousSubmodule_one_eq_span_X]
    exact hS f hf
  let L : Submodule F (σ → F) := (Submodule.span F S).comap ℓ
  let b := Module.finBasis F ((σ → F) ⧸ L)
  let r := Module.finrank F ((σ → F) ⧸ L)
  let θ : (σ → F) →ₗ[F] MvPolynomial (Fin r) F :=
    Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F)) ∘ₗ
      (b.equivFun.toLinearMap ∘ₗ L.mkQ)
  have hθ : ∀ v, θ v = ∑ i, b.equivFun (L.mkQ v) i • (X i : MvPolynomial (Fin r) F) := fun v => rfl
  let φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F := aeval (fun s => θ (Pi.single s 1))

  have key : ∀ c, φ (ℓ c) = θ c := by
    have : φ.toLinearMap ∘ₗ ℓ = θ := by
      refine LinearMap.pi_ext (fun s x => ?_)
      have hx : (Pi.single s x : σ → F) = x • Pi.single s (1 : F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, ℓ,
        Fintype.linearCombination_apply_single, map_smul, φ, aeval_X]
      rw [hx, map_smul]
    exact fun c => LinearMap.congr_fun this c

  let lift : Fin r → (σ → F) := fun i => (L.mkQ_surjective (b i)).choose
  have hlift : ∀ i, L.mkQ (lift i) = b i := fun i => (L.mkQ_surjective (b i)).choose_spec
  let ψ : MvPolynomial (Fin r) F →ₐ[F] MvPolynomial σ F := aeval (fun i => ℓ (lift i))
  have hφψ : φ.comp ψ = AlgHom.id F _ := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    have he : b.equivFun (b i) = Pi.single i 1 := by
      funext j
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    simp only [AlgHom.comp_apply, ψ, aeval_X, key, AlgHom.id_apply]
    rw [show θ (lift i) = Fintype.linearCombination F (fun i => (X i : MvPolynomial (Fin r) F))
      (b.equivFun (L.mkQ (lift i))) from rfl, hlift, he, Fintype.linearCombination_apply_single, one_smul]
  have hψθ : ∀ v, ψ (θ v) = ℓ (∑ i, b.equivFun (L.mkQ v) i • lift i) := by
    intro v
    rw [hθ, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, map_smul, aeval_X]
  have hspan : Submodule.span F S ≤ (Ideal.span S).restrictScalars F :=
    Submodule.span_le.mpr (fun f hf => Ideal.subset_span hf)
  refine ⟨r, φ, fun p => ⟨ψ p, by simpa using AlgHom.congr_fun hφψ p⟩, ?_, fun s => ?_⟩
  · apply le_antisymm
    · have hmk : (Ideal.Quotient.mkₐ F (Ideal.span S)).comp (ψ.comp φ) = Ideal.Quotient.mkₐ F (Ideal.span S) := by
        refine MvPolynomial.algHom_ext (fun s => ?_)
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        have h1 : φ (X s) = θ (Pi.single s 1) := aeval_X _ _
        rw [h1, hψθ]
        have hmem : (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) - Pi.single s 1 ∈ L := by
          rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
          have : (Submodule.Quotient.mk (∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • lift i) : (σ → F) ⧸ L) =
              ∑ i, b.equivFun (L.mkQ (Pi.single s 1)) i • b i := by
            rw [← Submodule.mkQ_apply, map_sum]
            simp only [map_smul, hlift]
          rw [this, b.sum_equivFun, Submodule.mkQ_apply, sub_self]
        have h2 := hspan hmem
        rw [map_sub] at h2
        have h3 : ℓ (Pi.single s 1) = X s := by
          simp [ℓ]
        rwa [h3] at h2
      intro f hf
      rw [RingHom.mem_ker] at hf
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := AlgHom.congr_fun hmk f
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← this, hf, map_zero, map_zero]
    · refine Ideal.span_le.mpr (fun f hf => ?_)
      obtain ⟨c, rfl⟩ := hSrange f hf
      have hc : c ∈ L := Submodule.subset_span hf
      show φ (ℓ c) = 0
      rw [key, hθ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).mpr hc]
      simp
  · rw [← mem_homogeneousSubmodule, homogeneousSubmodule_one_eq_span_X, ← Fintype.range_linearCombination]
    refine ⟨b.equivFun (L.mkQ (Pi.single s 1)), ?_⟩
    rw [show φ (X s) = θ (Pi.single s 1) from aeval_X _ _]
    rfl

end GroundTheory.Heights₂.Heights.Inter
