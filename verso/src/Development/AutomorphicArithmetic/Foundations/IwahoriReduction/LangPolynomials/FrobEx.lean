import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Set `e : 𝓞 ℚ ≃+* ℤ` to `Rat.ringOfIntegersEquiv`. Establish `hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ)`. Establish `hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible`. Apply `hmax.eq_of_le` to reduce the goal to its premises.

Introduce `htop`. Apply `v.isPrime.ne_top` to reduce the goal to its premises. Conclude with `(Ideal.map_eq_top_of_bijective _ e.bijective).1 htop`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Use `Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv` as an intermediate fact.

Simplify using `using this`. Unfold `normV`. Rewrite using `[Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]`.
-/
private theorem frobEx_norm {l : ℕ} (hl : l.Prime) {v : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = l := by
  haveI : Fact l.Prime := ⟨hl⟩
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
    apply hmax.eq_of_le
    · intro htop
      apply v.isPrime.ne_top
      exact (Ideal.map_eq_top_of_bijective _ e.bijective).1 htop
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv
      simpa using this
  unfold normV
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

/- English proof (translation)
Introduce `l _ _ Ω _ _ _ A hA`. Take `⟨v, hv, hlv⟩` from `hA`. Establish `hnorm : normV v = l` using `frobEx_norm Fact.out hlv`. Establish `hval : A.valuation (l : Ω) < 1`. Use `(hv (l : 𝓞 ℚ)).2 hlv` as an intermediate fact.

Simplify using `using this`. Use `⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ', GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_isFrob (F := ℚ) hv`. Rewrite `hσ` using `[hnorm]`. Take `⟨ι, hι, hιu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹`.

Establish `hfr : IsFrob A l (σ * ι)` using `isFrob_mul_of_mem_Ine hσ hι`. Use `⟨σ * ι, hfr.1, hfr, ?_⟩` and prove the remaining obligations. Unfold `cycBar`. Rewrite using `[MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]`.
-/
theorem UpperTheory.Kd.C7.pFrobEx :
    UpperTheory.Kd.C7.SFrobEx := by
  intro l _ _ Ω _ _ _ A hA
  obtain ⟨v, hv, hlv⟩ := hA
  have hnorm : normV v = l := frobEx_norm Fact.out hlv
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  refine ⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ',
    GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hv
  rw [hnorm] at hσ
  obtain ⟨ι, hι, hιu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹
  have hfr : IsFrob A l (σ * ι) := isFrob_mul_of_mem_Ine hσ hι
  refine ⟨σ * ι, hfr.1, hfr, ?_⟩
  unfold cycBar
  rw [MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]
