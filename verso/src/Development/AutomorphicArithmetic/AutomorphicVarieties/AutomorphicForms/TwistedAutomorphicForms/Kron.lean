import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

open NumberField IsDedekindDomain in
/- English proof (translation)
Introduce `K _ _`. Use `⟨NumberField.Units.torsionOrder K, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl hno haveI : Fact (Nat.Prime l) := ⟨hl⟩`. Rewrite using `[Nat.coprime_comm, hl.coprime_iff_not_dvd]`. Introduce `hdvd`.

Take `⟨g, hg⟩` from `exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd`. Establish `h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l`. Rewrite using `[← hg, ← Subgroup.orderOf_coe]`. Conclude with `IsPrimitiveRoot.orderOf _`. Establish `h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l` using `IsPrimitiveRoot.coe_units_iff.mpr h1`.

Establish `h3` using `h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)`. Conclude with `hno ⟨_, h3⟩`. Introduce `y hy hnorm`. Establish `hy' : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1` using `hy`. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by`.

Rewrite using `[← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]`. Conclude with `le_of_eq (hy' v))`. Establish `hI : IsIntegral ℤ (y : K)`. Use `NumberField.RingOfIntegers.isIntegral_coe r` as an intermediate fact. Rewrite `this` using `[hr]`. Then use the resulting hypothesis.

Take `⟨m, hm, hym⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm`. Establish `hrm : r ^ m = 1`. Apply `FaithfulSMul.algebraMap_injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[map_pow, hr, hym, map_one]`. Set `u : (𝓞 K)ˣ` to `Units.ofPowEqOne r m hrm hm.ne'`.

Establish `hu : u ∈ NumberField.Units.torsion K`. Rewrite using `[NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]`. Conclude with `⟨m, hm, Units.ext (by simp [u, hrm])⟩`. Rewrite `hu` using `[← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]`. Establish `hu'` using `congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_one] at hu'`. Express the relevant statement in the definitionally equal form `(u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'`. Establish `hur : (u : 𝓞 K) = r` using `Units.val_ofPowEqOne r m hrm hm.ne'`.

Rewrite `hu'` using `[hur]`. Rewrite using `[hu', map_one]`.
-/
theorem UpperTheory.V.Af.Tw.kron :
    UpperTheory.V.Af.Tw.Kron := by
  intro K _ _
  refine ⟨NumberField.Units.torsionOrder K, ?_, ?_⟩
  · intro l hl hno
    haveI : Fact (Nat.Prime l) := ⟨hl⟩
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd
    have h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact IsPrimitiveRoot.orderOf _
    have h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l := IsPrimitiveRoot.coe_units_iff.mpr h1
    have h3 := h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)
    exact hno ⟨_, h3⟩
  · intro y hy hnorm
    have hy' : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by
      rw [← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]
      exact le_of_eq (hy' v))
    have hI : IsIntegral ℤ (y : K) := by
      have := NumberField.RingOfIntegers.isIntegral_coe r
      rwa [hr] at this
    obtain ⟨m, hm, hym⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm
    have hrm : r ^ m = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_pow, hr, hym, map_one]
    let u : (𝓞 K)ˣ := Units.ofPowEqOne r m hrm hm.ne'
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨m, hm, Units.ext (by simp [u, hrm])⟩
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]
    have hu' := congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu'
    change (u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'
    have hur : (u : 𝓞 K) = r := Units.val_ofPowEqOne r m hrm hm.ne'
    rw [hur] at hu'
    rw [hu', map_one]
