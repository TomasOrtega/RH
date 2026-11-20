import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Establish `hS : ∑ i ∈ Finset.range n, ζ ^ i = 0`. Establish `hg` using `mul_geom_sum ζ n`. Rewrite `hg` using `[h, sub_self]`. Conclude with `(mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)`. Establish `hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i)`.

Rewrite using `[Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]`. Rewrite using `[hn]`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `i _`. Establish `hd` using `sub_dvd_pow_sub_pow ζ 1 i`.

Rewrite `hd` using `[one_pow]`. Rewrite using `[← neg_sub (ζ ^ i) 1]`. Conclude with `(dvd_neg).mpr hd`.
-/
private theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (h : ζ ^ n = 1) (h1 : ζ ≠ 1) :
    ζ - 1 ∣ (n : O) := by
  have hS : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have hg := mul_geom_sum ζ n
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)
  have hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  rw [hn]
  apply Finset.dvd_sum
  intro i _
  have hd := sub_dvd_pow_sub_pow ζ 1 i
  rw [one_pow] at hd
  rw [← neg_sub (ζ ^ i) 1]
  exact (dvd_neg).mpr hd

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ n hn`. Take `⟨hiO, -, -, -, -, -, -, hvO, hunit⟩` from `dvrFacts l O`. Establish `hp : l.Prime` using `Fact.out`. Establish `hl0 : (l : ℤ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hlO : (l : O) ≠ 0`.

Introduce `h`. Apply `hl0` to reduce the goal to its premises. Apply `hiO` to reduce the goal to its premises. Rewrite using `[map_natCast, h, map_zero]`. Establish `hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O`.

Establish `hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O)` using `hunit _ (Nat.not_dvd_ordCompl hp hn)`. Use `conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]`. Rewrite using `[Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu, add_zero, hvO, nsmul_eq_mul]`. Use `⟨hval, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ζ hζ h1`.

Rewrite using `[← hval]`. Conclude with `(IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)`. Rewrite using `[hvO]`. Conclude with `fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)`. Conclude with `charZero_of_injective_algebraMap hiO`.
-/
theorem UpperTheory.V.Chr.rootVal :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (n : ℕ), n ≠ 0 → IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O ∧
          (∀ ζ : O, ζ ^ n = 1 → ζ ≠ 1 → IsDiscreteValuationRing.addVal O (ζ - 1) ≤ (n.factorization l : ℕ∞) * eO l O) ∧ eO l O ≠ ⊤ ∧ CharZero O := by
  intro l _ O _ _ _ _ _ n hn
  obtain ⟨hiO, -, -, -, -, -, -, hvO, hunit⟩ := dvrFacts l O
  have hp : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O := by
    have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O) := hunit _ (Nat.not_dvd_ordCompl hp hn)
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]
    rw [Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu,
      add_zero, hvO, nsmul_eq_mul]
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro ζ hζ h1
    rw [← hval]
    exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)
  · rw [hvO]
    exact fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  · exact charZero_of_injective_algebraMap hiO
