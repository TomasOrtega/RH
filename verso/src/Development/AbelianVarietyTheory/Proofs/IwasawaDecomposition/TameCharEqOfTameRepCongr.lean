import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharacterIndependentUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameRepConjugateInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu`. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P` from `exists_isPlaceOver Ω P`. Take `⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩` from `GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ`. Take `⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩` from `GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'`. Establish `hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b`.

Introduce `a b`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]`. Rewrite using `[← hconj ρ σ, ← hconj ρ' σ']`. Use `set s := ρ⁻¹ * σ * ρ`. Use `set s' := ρ'⁻¹ * σ' * ρ'`.

Use `set m := normV P - 1`. Rewrite `hv`, `hv'` using `[zpow_one]`. Rewrite `hv'` using `[← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs']`. Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hϖ2 (Submodule.zero_mem _)`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow hm.ne', eq_comm, map_eq_zero]`. Conclude with `hϖ0 (by exact_mod_cast hπ)`.

Establish `hroot : ∀ t : G E Ω, (t π / π) ^ m = 1`. Introduce `t`. Rewrite using `[div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]`. Establish `hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal`. Introduce `x`.

Conclude with `hA x`. Establish `hmv : ¬ A.valuation (m : Ω) < 1`. Introduce `h`. Apply `hmP` to reduce the goal to its premises. Rewrite using `[← hlt]`.

Simplify using `using h`. Establish `hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1`. Use `(hlt (u - u')).2 huu` as an intermediate fact. Simplify using `using this`. Establish `heq : s π / π = s' π / π`.

Use `root_eq_of_close A m (hroot s) (hroot s') hmv ?_` and prove the remaining obligations. Establish `e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E)) + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E))` using `by ring`. Rewrite using `[e]`. Conclude with `Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'`. Conclude with `GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs' ((div_left_inj' hπ0).1 heq)`.
-/
theorem char_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P := exists_isPlaceOver Ω P
  obtain ⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ
  obtain ⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'
  have hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b := by
    intro a b
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [← hconj ρ σ, ← hconj ρ' σ']
  set s := ρ⁻¹ * σ * ρ
  set s' := ρ'⁻¹ * σ' * ρ'
  set m := normV P - 1
  rw [zpow_one] at hv hv'
  rw [← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs'] at hv'
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Submodule.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  have hroot : ∀ t : G E Ω, (t π / π) ^ m = 1 := by
    intro t
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal := by
    intro x
    exact hA x
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hlt]
    simpa using h
  have hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
    have := (hlt (u - u')).2 huu
    simpa using this
  have heq : s π / π = s' π / π := by
    refine root_eq_of_close A m (hroot s) (hroot s') hmv ?_
    have e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E))
        + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'
  exact GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs'
    ((div_left_inj' hπ0).1 heq)

end GlobalTheory.TameTau
