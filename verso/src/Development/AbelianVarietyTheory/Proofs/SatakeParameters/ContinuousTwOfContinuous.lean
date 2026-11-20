import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

/- English proof (translation)
Establish `hP : (Ideal.span {(l : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥ (by`. Introduce `x hx`. Establish `: x = 0` using `(algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)`. Simplify using `[this])`.

Establish `hmem : ((l : ℕ) : 𝓞 K) ∈ Q`. Establish `: (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K))` using `hQc ▸ Ideal.mem_span_singleton_self _`. Simplify using `using this`. Establish `hne : Q ≠ ⊥`. Introduce and unpack `rfl`.

Establish `h0 : ((l : ℕ) : 𝓞 K) = 0` using `by simpa using hmem`. Establish `: ((l : ℕ) : 𝓞 K) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Conclude with `this h0`. Conclude with `⟨⟨Q, hQ, hne⟩, hmem⟩`.
-/
theorem exists_place_dvd_prime {K : Type} [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(l : ℤ)}) ⊥
    (by
      intro x hx
      have : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by simpa using hx)
      simp [this])
  have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : ((l : ℕ) : 𝓞 K) = 0 := by simpa using hmem
    have : ((l : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    exact this h0
  exact ⟨⟨Q, hQ, hne⟩, hmem⟩

/- English proof (translation)
Establish `h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val`. Simplify using `only [UpperTheory.V.Af.tw_val]`. Conclude with `(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)`. Use `Units.continuous_iff.2 ⟨h1, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`.

Conclude with `h1.comp continuous_inv`.
-/
theorem continuous_tw_of_continuous {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {k : Type} [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {μ : Γ →* kˣ} (hr : Continuous r) (hμ : Continuous μ) :
    Continuous (UpperTheory.V.Af.tw r μ) := by
  have h1 : Continuous fun s => (UpperTheory.V.Af.tw r μ s).val := by
    simp only [UpperTheory.V.Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  simp only [← map_inv]
  exact h1.comp continuous_inv

/- English proof (translation)
Introduce `hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs`. Take `⟨w₀, hw₀⟩` from `exists_place_dvd_prime (K := E) l`. Establish `hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀`. Assume the negation of the conclusion as `h`. Conclude with `(hs.2.2.2.2 w₀ h).1 hw₀`.

Take `⟨κ, m, hκ, -, hs'⟩` from `GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hA E l a ha π χ hs w₀ hsplit`. Take `⟨r', hr'c, hr'⟩` from `hcsd E Ω l ι a ha (π.twist κ) _ hs'`. Establish `hκi : (κ⁻¹).IsAlg (-m)` using `fun k => by`. Rewrite using `[HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]`. Conclude with `Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm`.

Take `⟨art, hart, hμ⟩` from `(GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt GlobalTheory.globalArtinReciprocity_holds).1 E Ω`. Take `⟨μ, ⟨hμc, hμ⟩, -⟩` from `hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)`. Use `⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩` and prove the remaining obligations. Establish `h` using `UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ`. Rewrite `h` using `[← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]`. Then use the resulting hypothesis.
-/
theorem ex_good_of_ex_csd : AutomorphicFormsFiniteGL → Ex .csd → Ex .good := by
  intro hA hcsd E Ω _ _ _ _ _ _ l _ ι a ha π χ hs
  obtain ⟨w₀, hw₀⟩ := exists_place_dvd_prime (K := E) l
  have hsplit : GlobalTheory.UnitaryBC.IsSplitAt w₀ := by
    by_contra h
    exact (hs.2.2.2.2 w₀ h).1 hw₀
  obtain ⟨κ, m, hκ, -, hs'⟩ := GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified hA E l a ha π χ hs w₀ hsplit
  obtain ⟨r', hr'c, hr'⟩ := hcsd E Ω l ι a ha (π.twist κ) _ hs'
  have hκi : (κ⁻¹).IsAlg (-m) := fun k => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hκ k, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨art, hart, hμ⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ⁻¹ (-m) (isAlgPos_of_isAlg hκi)
  refine ⟨UpperTheory.V.Af.tw r' μ, continuous_tw_of_continuous hr'c hμc, ?_⟩
  have h := UpperTheory.V.Af.Cq.attTwist E Ω l ι a r' (π.twist κ) hr' art κ⁻¹ (-m) μ hart hμ
  rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GalCut
