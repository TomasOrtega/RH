import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.NormOneCount

/- English proof (translation)
Proceed by induction on `n using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p k hp hk`. Take `⟨k, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[Nat.totient_prime_pow_succ hp]`. Establish `h2` using `hp.two_le`.

Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`. Establish `hq : 1 ≤ q` using `by omega`. Establish `hP : 1 ≤ (q + 1) ^ k` using `Nat.one_le_pow _ _ (by omega)`. Rewrite using `[pow_succ, Nat.add_sub_cancel]`. Generalize the expression as in `(q + 1) ^ k = P at hP ⊢`.

Establish `hPP : P ≤ P ^ 2` using `by nlinarith`. Use `⟨?_, fun ho => ?_⟩` and prove the remaining obligations. Establish `h1 : q + 1 ≤ 2 * q ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `ho' : Odd (q + 1)` using `(Nat.odd_mul.1 ho).2`.

Establish `hq2 : 2 ≤ q`. Take `⟨m, hm⟩` from `ho'`. Use linear arithmetic over natural numbers and integers. Establish `h1 : q + 1 ≤ q ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `coprime a b ha hb hab iha ihb`. Rewrite using `[Nat.totient_mul hab]`. Use `⟨?_, fun ho => ?_⟩` and prove the remaining obligations.

Break down `Nat.even_or_odd a with hea | hoa` into its components or cases. Establish `hob : Odd b`. Break down `Nat.even_or_odd b with heb | hob` into its components or cases. Use `Nat.dvd_gcd hea.two_dvd heb.two_dvd` as an intermediate fact. Rewrite `this` using `[hab.gcd_eq_one]`.

Use linear arithmetic over natural numbers and integers. Conclude with `hob`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Take `⟨h1, h2⟩` from `Nat.odd_mul.1 ho`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 := hp.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hP : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, Nat.add_sub_cancel]
    generalize (q + 1) ^ k = P at hP ⊢
    have hPP : P ≤ P ^ 2 := by nlinarith
    refine ⟨?_, fun ho => ?_⟩
    · have h1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * (2 * q ^ 2) := Nat.mul_le_mul hPP h1
        _ = _ := by ring
    · have ho' : Odd (q + 1) := (Nat.odd_mul.1 ho).2
      have hq2 : 2 ≤ q := by
        obtain ⟨m, hm⟩ := ho'
        omega
      have h1 : q + 1 ≤ q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * q ^ 2 := Nat.mul_le_mul hPP h1
        _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    refine ⟨?_, fun ho => ?_⟩
    · rcases Nat.even_or_odd a with hea | hoa
      · have hob : Odd b := by
          rcases Nat.even_or_odd b with heb | hob
          · have := Nat.dvd_gcd hea.two_dvd heb.two_dvd
            rw [hab.gcd_eq_one] at this
            omega
          · exact hob
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hob)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hoa) ihb.1
          _ = _ := by ring
    · obtain ⟨h1, h2⟩ := Nat.odd_mul.1 ho
      calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)
        _ = _ := by ring

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)`. Establish `h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K))` using `hg ▸ IsPrimitiveRoot.orderOf g`. Establish `h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K))` using `h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective`. Establish `h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K))` using `IsPrimitiveRoot.coe_units_iff.2 h2`. Establish `h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K))` using `h3.map_of_injective (RingOfIntegers.coe_injective)`.

Establish `hpos : 0 < Nat.card (Units.torsion K)` using `Nat.card_pos`. Establish `h5` using `IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4 (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)`. Rewrite `h5` using `[Nat.lcm_self]`. Conclude with `(le_totient_sq _).1.trans (by gcongr)`.
-/
theorem card_torsion_le (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K)) := hg ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K)) :=
    h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective
  have h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K)) :=
    IsPrimitiveRoot.coe_units_iff.2 h2
  have h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K)) :=
    h3.map_of_injective (RingOfIntegers.coe_injective)
  have hpos : 0 < Nat.card (Units.torsion K) := Nat.card_pos
  have h5 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4
    (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self] at h5
  exact (le_totient_sq _).1.trans (by gcongr)

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hne : ipow 𝔞 1 ≠ ⊥`. Unfold `ipow`. Rewrite using `[zpow_one]`. Introduce `h0`. Conclude with `(FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)`.

Establish `hfg : (ipow 𝔞 1).FG`. Unfold `ipow`. Conclude with `FractionalIdeal.fg_of_isNoetherianRing le_rfl _`. Establish `h1 : IsIntegral (𝓞 K) u` using `isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)`. Conclude with `isIntegral_trans u h1`.
-/
theorem isIntegral_of_mul_mem {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by
  have hne : ipow 𝔞 1 ≠ ⊥ := by
    unfold ipow
    rw [zpow_one]
    intro h0
    exact (FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  have hfg : (ipow 𝔞 1).FG := by
    unfold ipow
    exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : IsIntegral (𝓞 K) u :=
    isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)
  exact isIntegral_trans u h1

/- English proof (translation)
Establish `hc0 : c ≠ 0` using `left_ne_zero_of_mul_eq_one hc`. Establish `hd0 : d ≠ 0` using `left_ne_zero_of_mul_eq_one hd`. Establish `i1 : IsIntegral ℤ (c / d)` using `isIntegral_of_mul_mem h fun t ht => by`. Rewrite using `[← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht`. Establish `i2 : IsIntegral ℤ (d / c)` using `isIntegral_of_mul_mem h fun t ht => by`.

Rewrite using `[← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht`. Take `⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d` from `⟨⟨c / d, i1⟩, rfl⟩`. Take `⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c` from `⟨⟨d / c, i2⟩, rfl⟩`. Establish `hm : a * b = 1`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one, ha, hb]`. Clear the denominators using the available nonvanishing facts. Establish `hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1` using `fun φ e he => by`. Establish `h3` using `congrArg (fun z => ‖φ z‖) he`. Simplify using `only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3`.

Use polynomial arithmetic with `[norm_nonneg (φ e)]`. Use `⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show w (algebraMap (𝓞 K) K a) = 1`. Rewrite using `[ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]`. Use `show c = algebraMap (𝓞 K) K a * d`.

Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_torsion [StarRing K] (hK : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    {𝔞 𝔞' : Ideal (𝓞 K)} (h : 𝔞' ≠ ⊥) {c d : K} (hc : c * star c = 1) (hd : d * star d = 1)
    (h1 : ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) (h2 : ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) :
    ∃ ζ : Units.torsion K, c = algebraMap (𝓞 K) K ((ζ : (𝓞 K)ˣ) : 𝓞 K) * d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have i1 : IsIntegral ℤ (c / d) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht
  have i2 : IsIntegral ℤ (d / c) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d := ⟨⟨c / d, i1⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c := ⟨⟨d / c, i2⟩, rfl⟩
  have hm : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, ha, hb]
    field_simp
  have hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1 := fun φ e he => by
    have h3 := congrArg (fun z => ‖φ z‖) he
    simp only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3
    nlinarith [norm_nonneg (φ e)]
  refine ⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩
  · show w (algebraMap (𝓞 K) K a) = 1
    rw [ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]
  · show c = algebraMap (𝓞 K) K a * d
    rw [ha]
    field_simp

/- English proof (translation)
Introduce `K _ _ _ hK x hx`. Take `⟨hfin, hle⟩` from `Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K x hx`. Use `set A := {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} with hA`. Set `c0 : Ideal (𝓞 K) × Ideal (𝓞 K) → K` to `fun p => if h : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow p.1 1 ↔ t ∈ ipow p.2 1 then h.choose else 0`. Set `g : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Units.torsion K → K` to `fun q => algebraMap (𝓞 K) K ((q.2 : (𝓞 K)ˣ) : 𝓞 K) * c0 q.1`.

Establish `hB : ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))).Finite` using `(hfin.prod hfin).prod Set.finite_univ`. Establish `hsub : {c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1} ⊆ g '' ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K)))`. Introduce and unpack `c ⟨hc, 𝔞, 𝔞', h1, h2, h3, h4, h5⟩`. Establish `hex : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1` using `⟨c, hc, h5⟩`. Take `⟨ζ, hζ⟩` from `exists_torsion hK.2.1 h2 hc hex.choose_spec.1 h5 hex.choose_spec.2`.

Use `⟨((𝔞, 𝔞'), ζ), ⟨⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, trivial⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [g, c0, dif_pos hex]`. Conclude with `hζ.symm`. Establish `henc` using `(Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)`. Rewrite `henc` using `[← hB.cast_ncard_eq, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ]`.

Use `(ENat.toENNReal_le.2 henc).trans ?_` and prove the remaining obligations. Rewrite using `[ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K`. Use `hK.1` as an intermediate fact.

Rewrite using `[IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Establish `hw : (Nat.card (Units.torsion K) : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2`. Establish `h1` using `card_torsion_le K`. Rewrite `h1` using `[hd]`. Establish `h2 : (Nat.card (Units.torsion K) : ℝ) ≤ 2 * (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) ^ 2`.

Conclude with `h1` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA' : (A.ncard : ℝ) ≤ x ^ (2 + cf K)` using `hle.trans (Real.rpow_le_rpow_of_exponent_le hx (by unfold cf; linarith))`. Establish `hx0 : 0 < x` using `by linarith`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ x : ℝ, 1 ≤ x → ((({c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * x ^ (2 * (2 + cf K))) := by
  intro K _ _ _ hK x hx
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K x hx
  set A := {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} with hA
  let c0 : Ideal (𝓞 K) × Ideal (𝓞 K) → K := fun p =>
    if h : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow p.1 1 ↔ t ∈ ipow p.2 1 then h.choose else 0
  let g : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Units.torsion K → K := fun q =>
    algebraMap (𝓞 K) K ((q.2 : (𝓞 K)ˣ) : 𝓞 K) * c0 q.1
  have hB : ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))).Finite :=
    (hfin.prod hfin).prod Set.finite_univ
  have hsub : {c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧
      (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1} ⊆
      g '' ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))) := by
    rintro c ⟨hc, 𝔞, 𝔞', h1, h2, h3, h4, h5⟩
    have hex : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := ⟨c, hc, h5⟩
    obtain ⟨ζ, hζ⟩ := exists_torsion hK.2.1 h2 hc hex.choose_spec.1 h5 hex.choose_spec.2
    refine ⟨((𝔞, 𝔞'), ζ), ⟨⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, trivial⟩, ?_⟩
    simp only [g, c0, dif_pos hex]
    exact hζ.symm
  have henc := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  rw [← hB.cast_ncard_eq, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ] at henc
  refine (ENat.toENNReal_le.2 henc).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hw : (Nat.card (Units.torsion K) : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 := by
    have h1 := card_torsion_le K
    rw [hd] at h1
    have h2 : (Nat.card (Units.torsion K) : ℝ) ≤ 2 * (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) ^ 2 := by
      exact_mod_cast h1
    linarith
  have hA' : (A.ncard : ℝ) ≤ x ^ (2 + cf K) :=
    hle.trans (Real.rpow_le_rpow_of_exponent_le hx (by unfold cf; linarith))
  have hx0 : 0 < x := by linarith
  push_cast
  calc (A.ncard : ℝ) * A.ncard * Nat.card (Units.torsion K)
      ≤ x ^ (2 + cf K) * x ^ (2 + cf K) * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hx0, two_mul (2 + cf K)]; ring

end GlobalTheory.DegCnt.NormOneCount
