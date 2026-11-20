import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

open NumberField IsDedekindDomain Formalism.BasicNotions

/- English proof (translation)
Establish `hint : IsAlgebraic ℚ H.sqd` using `(Algebra.IsIntegral.isIntegral (R := ℚ) H.sqd).isAlgebraic`. Establish `hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqd}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]`. Conclude with `x.2`. Establish `hle : Algebra.adjoin ℚ {H.sqd} ≤ AlgHom.equalizer (σ : H.E →ₐ[ℚ] H.E) (AlgHom.id ℚ H.E)`.

Rewrite using `[Algebra.adjoin_le_iff, Set.singleton_subset_iff]`. Conclude with `hσ`. Conclude with `hle hx`.
-/
private theorem fixK {R : Ranks} (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E) (hσ : σ H.sqd = H.sqd) (x : H.K) :
    σ (x : H.E) = x := by
  have hint : IsAlgebraic ℚ H.sqd := (Algebra.IsIntegral.isIntegral (R := ℚ) H.sqd).isAlgebraic
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint]
    exact x.2
  have hle : Algebra.adjoin ℚ {H.sqd} ≤
      AlgHom.equalizer (σ : H.E →ₐ[ℚ] H.E) (AlgHom.id ℚ H.E) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact hσ
  exact hle hx

/- English proof (translation)
Rewrite using `[← Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx]`. Simplify `g.2` using `[Formalism.BasicNotions.Host.sigmaOf, Formalism.HC.HostRaw.galE]`.
-/
private theorem sigma_sqd {R : Ranks} (H : Host R) (g : R.Psi) : H.sigmaOf (g : R.GG) H.sqd = H.sqd := by
  rw [← Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx]
  simpa [Formalism.BasicNotions.Host.sigmaOf, Formalism.HC.HostRaw.galE] using g.2

private noncomputable def galK {R : Ranks} (H : Host R) (g : R.Psi) : H.E ≃ₐ[H.K] H.E :=
  AlgEquiv.ofRingEquiv (f := (H.sigmaOf (g : R.GG)).toRingEquiv) (fun y => fixK H _ (sigma_sqd H g) y)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `g₁ g₂ h`. Establish `h' : H.sigmaOf (g₁ : R.GG) = H.sigmaOf (g₂ : R.GG)`. Use extensionality with `y`. Conclude with `congrArg (fun f : H.E ≃ₐ[H.K] H.E => f y) h`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `h'` using `[Formalism.BasicNotions.Host.sigmaOf]`. Introduce `τ`. Establish `hτ : (τ.restrictScalars ℚ) H.sqd = H.sqd`. Use `τ.commutes (⟨H.sqd, H.sqd_mem_K⟩ : H.K)` as an intermediate fact.

Simplify using `using this`. Use `⟨⟨H.gal (τ.restrictScalars ℚ), ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx _).mpr hτ`. Use extensionality with `y`. Simplify using `[galK, Formalism.BasicNotions.Host.sigmaOf]`.
-/
private theorem galK_bij {R : Ranks} (H : Host R) : Function.Bijective (galK H) := by
  constructor
  · intro g₁ g₂ h
    have h' : H.sigmaOf (g₁ : R.GG) = H.sigmaOf (g₂ : R.GG) := by
      ext y
      exact congrArg (fun f : H.E ≃ₐ[H.K] H.E => f y) h
    apply Subtype.ext
    simpa [Formalism.BasicNotions.Host.sigmaOf] using h'
  · intro τ
    have hτ : (τ.restrictScalars ℚ) H.sqd = H.sqd := by
      have := τ.commutes (⟨H.sqd, H.sqd_mem_K⟩ : H.K)
      simpa using this
    refine ⟨⟨H.gal (τ.restrictScalars ℚ), ?_⟩, ?_⟩
    · exact (Formalism.HC.HostAx.galE_mem_Psi_iff H.toHostAx _).mpr hτ
    · ext y
      simp [galK, Formalism.BasicNotions.Host.sigmaOf]

/- English proof (translation)
Introduce `R H ι _ eT`. Use `haveI : IsGalois ℚ H.E := H.galois`. Use `haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E`. Establish `hnorm : ∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x)`. Introduce `x`.

Rewrite using `[Algebra.norm_eq_prod_automorphisms]`. Conclude with `Fintype.prod_bijective (fun τ => galK H (eT τ)) ((galK_bij H).comp eT.bijective) _ _ (fun τ => rfl)`. Use `⟨hnorm, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Establish `h1` using `hnorm z`.

Rewrite `h1` using `[H.der.norm_mu z hz, map_one]`. Simplify using `only [zpow_one, Formalism.BasicNotions.Host.emb, RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[← map_prod, h1, map_one]`.
-/
theorem UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi),
      (∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x)) ∧
      UpperTheory.MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := by
  intro R H ι _ eT
  haveI : IsGalois ℚ H.E := H.galois
  haveI : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have hnorm : ∀ x : H.E, ∏ τ, H.sigmaOf ((eT τ : R.Psi) : R.GG) x =
      algebraMap H.K H.E (Algebra.norm H.K x) := by
    intro x
    rw [Algebra.norm_eq_prod_automorphisms]
    exact Fintype.prod_bijective (fun τ => galK H (eT τ)) ((galK_bij H).comp eT.bijective)
      _ _ (fun τ => rfl)
  refine ⟨hnorm, ?_⟩
  intro z hz
  have h1 := hnorm z
  rw [H.der.norm_mu z hz, map_one] at h1
  simp only [zpow_one, Formalism.BasicNotions.Host.emb, RingHom.comp_apply, RingHom.coe_coe]
  rw [← map_prod, h1, map_one]
