import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def ClassTermBound : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * (T / Ω))

def ClassTermBoundBeta : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ → ∀ Λ : PeriodPair, Λ.ω₁ = 1 → Λ.ω₂ = (1 + Complex.I * (Real.sqrt H.d : ℝ)) / 2 →
      ∀ l : ℕ, l.Prime → ∃ N : ℕ, ∀ Q : Finset (HeightOneSpectrum (OF H.E)),
      IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF H.E) ∉ q.asIdeal) → ∀ (y : (Af H.E)ˣ) (T : ℂ),
        IsClassTerm φ s κ (condQ 𝔣 Q) χ y T → IntAt l ((l : ℂ) ^ N * beta H.E H.d s κ Λ T)

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Use `⟨n, hn, IsIntegral.of_pow hm ?_⟩` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `h1 : IsIntegral ℤ ((n : ℂ) ^ m)` using `(isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))).pow m |> fun h => by simpa using h`. Establish `e : ((n : ℂ) * a) ^ (m + 1) = (n : ℂ) ^ m * ((n : ℂ) * a ^ (m + 1))` using `by ring`.

Rewrite using `[e]`. Conclude with `h1.mul h`.
-/
theorem intAt_of_pow {l m : ℕ} (hm : 0 < m) {a : ℂ} (h : IntAt l (a ^ m)) : IntAt l a := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, IsIntegral.of_pow hm ?_⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : IsIntegral ℤ ((n : ℂ) ^ m) := (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))).pow m |> fun h => by simpa using h
  have e : ((n : ℂ) * a) ^ (m + 1) = (n : ℂ) ^ m * ((n : ℂ) * a ^ (m + 1)) := by ring
  rw [e]
  exact h1.mul h

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `h1 : IsIntegral ℤ (k : ℂ)` using `by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))`. Rewrite using `[mul_left_comm]`. Conclude with `h1.mul h`.
-/
theorem intAt_natMul {l : ℕ} (k : ℕ) {a : ℂ} (h : IntAt l a) : IntAt l ((k : ℂ) * a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  have h1 : IsIntegral ℤ (k : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (k : ℤ))
  rw [mul_left_comm]
  exact h1.mul h

def ringPair (d : ℕ) (hd : 0 < d) : PeriodPair where
  ω₁ := 1
  ω₂ := (1 + Complex.I * (Real.sqrt d : ℝ)) / 2
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp at hi hr
    have hb : b = 0 := by
      rcases hi with hi | hi
      · exact hi
      · omega
    subst hb
    simpa using hr

/- English proof (translation)
Introduce `R H I _ φ s κ 𝔣 χ hD`. Establish `hd : 0 < H.d` using `H.hypOdd.2.1.pos`. Use `set Λ := ringPair H.d hd`. Establish `hC : ((C0 H.E H.d (2 * s) κ : ℝ) : ℂ) ≠ 0`. Use `hD.2.2.1` as an intermediate fact.

Conclude with `(cmValueConst_pos H.E hd (by omega) κ).ne'` after adjusting the coercions. Establish `hΔ : latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0` using `pow_ne_zero _ (latDisc_ne_zero Λ)`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_pow_nat_eq (latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) (n := 12) (by norm_num)`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hΔ (by rw [← hz]; simp)`. Use `⟨z / C0 H.E H.d (2 * s) κ, div_ne_zero hz0 hC, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `h R H I φ s κ 𝔣 χ hD Λ rfl rfl l hl`. Use `⟨N, fun Q hQ hQl y T hT => intAt_of_pow (m := 12) (by norm_num) ?_⟩` and prove the remaining obligations. Use `intAt_natMul (l ^ (11 * N)) (hN Q hQ hQl y T hT)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Unfold `beta`. Rewrite using `[← hz]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem classTermBound_of_beta (h : ClassTermBoundBeta) : ClassTermBound := by
  intro R H I _ φ s κ 𝔣 χ hD
  have hd : 0 < H.d := H.hypOdd.2.1.pos
  set Λ := ringPair H.d hd
  have hC : ((C0 H.E H.d (2 * s) κ : ℝ) : ℂ) ≠ 0 := by
    have := hD.2.2.1
    exact_mod_cast (cmValueConst_pos H.E hd (by omega) κ).ne'
  have hΔ : latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (latDisc_ne_zero Λ)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) (n := 12) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hz]; simp)
  refine ⟨z / C0 H.E H.d (2 * s) κ, div_ne_zero hz0 hC, fun l hl => ?_⟩
  obtain ⟨N, hN⟩ := h R H I φ s κ 𝔣 χ hD Λ rfl rfl l hl
  refine ⟨N, fun Q hQ hQl y T hT => intAt_of_pow (m := 12) (by norm_num) ?_⟩
  have := intAt_natMul (l ^ (11 * N)) (hN Q hQ hQl y T hT)
  convert this using 1
  unfold beta
  rw [← hz]
  push_cast
  field_simp
  ring

section Integral

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l : ℕ}

/- English proof (translation)
Take `⟨n, hn, h⟩` from `h`. Establish `hu : IsUnit (n : O)`. Assume the negation of the conclusion as `hu`. Establish `hn' : (n : O) ∈ IsLocalRing.maximalIdeal O` using `hu`. Take `⟨x, y, hxy⟩` from `Nat.isCoprime_iff_coprime.2 hn`.

Establish `h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O`. Establish `: (x : O) * n + (y : O) * l = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → O) hxy`. Rewrite using `[← this]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hn') (Ideal.mul_mem_left _ _ hl)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.

Establish `h2 : IsIntegral O (ι ((n : ℂ) * a))` using `h.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)`. Take `⟨v, hv⟩` from `hu.exists_left_inv`. Establish `h3` using `(isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := v)).mul h2`. Establish `h4` using `congrArg (algebraMap O (AlgebraicClosure (FractionRing O))) hv`. Rewrite `h4` using `[map_mul, map_natCast, map_one]`.

Rewrite `h3` using `[map_mul, map_natCast, ← mul_assoc, h4, one_mul]`. Then use the resulting hypothesis.
-/
theorem isIntegral_of_intAt (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (ι : ℂ →+* AlgebraicClosure (FractionRing O)) {a : ℂ}
    (h : IntAt l a) : IsIntegral O (ι a) := by
  obtain ⟨n, hn, h⟩ := h
  have hu : IsUnit (n : O) := by
    by_contra hu
    have hn' : (n : O) ∈ IsLocalRing.maximalIdeal O := hu
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hn
    have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : (x : O) * n + (y : O) * l = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hxy
      rw [← this]
      exact add_mem (Ideal.mul_mem_left _ _ hn') (Ideal.mul_mem_left _ _ hl)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have h2 : IsIntegral O (ι ((n : ℂ) * a)) := h.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := v)).mul h2
  have h4 := congrArg (algebraMap O (AlgebraicClosure (FractionRing O))) hv
  rw [map_mul, map_natCast, map_one] at h4
  rwa [map_mul, map_natCast, ← mul_assoc, h4, one_mul] at h3

/- English proof (translation)
Establish `ha : IsAlgebraic O u` using `(IsFractionRing.isAlgebraic_iff O (FractionRing O) _).2 (Algebra.IsAlgebraic.isAlgebraic u)`. Take `⟨y, hy, hint⟩` from `ha.exists_integral_multiple`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ`. Rewrite `hl` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `hl`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h3` using `(isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := c ^ n * (↑v⁻¹ : O))).mul hint`. Use `(congrArg (IsIntegral O) ?_).mpr h3` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, ← mul_assoc, ← map_mul, ← map_natCast (algebraMap O (AlgebraicClosure (FractionRing O))), ← map_pow, hc]`.

Use `congr 2`. Rewrite using `[mul_assoc, ← mul_assoc (↑v⁻¹ : O), Units.inv_mul, one_mul, mul_pow, mul_comm]`.
-/
theorem exists_pow_mul_isIntegral (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (u : AlgebraicClosure (FractionRing O)) :
    ∃ M : ℕ, IsIntegral O ((l : AlgebraicClosure (FractionRing O)) ^ M * u) := by
  have ha : IsAlgebraic O u :=
    (IsFractionRing.isAlgebraic_iff O (FractionRing O) _).2 (Algebra.IsAlgebraic.isAlgebraic u)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hl
  refine ⟨n, ?_⟩
  have h3 := (isIntegral_algebraMap (R := O) (A := AlgebraicClosure (FractionRing O)) (x := c ^ n * (↑v⁻¹ : O))).mul hint
  refine (congrArg (IsIntegral O) ?_).mpr h3
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← map_natCast (algebraMap O (AlgebraicClosure (FractionRing O))), ← map_pow, hc]
  congr 2
  rw [mul_assoc, ← mul_assoc (↑v⁻¹ : O), Units.inv_mul, one_mul, mul_pow, mul_comm]

/- English proof (translation)
The claim follows from `IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).injective).1 h)`.
-/
theorem exists_eq_of_isIntegral {x : FractionRing O}
    (h : IsIntegral O (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O)) x)) :
    ∃ y : O, algebraMap O (FractionRing O) y = x :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((isIntegral_algebraMap_iff (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).injective).1 h)

end Integral

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

/- English proof (translation)
Take `⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, -, hth⟩` from `ht`. Take `⟨Ω, hΩ, hb⟩` from `h D.R D.host I φ s κ 𝔣 χ hD`. Take `⟨n, hn⟩` from `hb (X.l i) (X.lPrime i).out`. Take `⟨M, hM⟩` from `exists_pow_mul_isIntegral (X.O_l i) (u * ι Ω)`. Use `⟨M + n, fun Q hQ δ => exists_eq_of_isIntegral ?_⟩` and prove the remaining obligations.

Take `⟨hfin, π, T, -, hT, hδ⟩` from `hth Q hQ`. Take `⟨h1, h2⟩` from `placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣`. Establish `hf : ({q | π q⁻¹ = δ} : Set (PicO (condQ 𝔣 (belowSet Q)))).Finite` using `Set.toFinite _`. Establish `hs : IsIntegral (X.O i) (∑ q ∈ hf.toFinset, ι (((X.l i : ℕ) : ℂ) ^ n * (T q / Ω)))` using `IsIntegral.sum _ fun q _ => isIntegral_of_intAt (X.O_l i) ι (hn _ h1 h2 _ _ (hT q))`. Use `(congrArg (IsIntegral (X.O i)) ?_).mpr (hM.mul hs)` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, map_natCast, hδ, finsum_mem_eq_finite_toFinset_sum _ hf, ← map_sum, ← Finset.mul_sum, ← Finset.sum_div, map_mul, map_pow, map_natCast, map_div₀]`. Establish `: ι Ω ≠ 0` using `(map_ne_zero ι).2 hΩ`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_bound_at (h : ClassTermBound) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) :
    ∃ n : ℕ, ∀ Q, BlochKatoReduction.Gen.QOk X i Q → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
      ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, -, hth⟩ := ht
  obtain ⟨Ω, hΩ, hb⟩ := h D.R D.host I φ s κ 𝔣 χ hD
  obtain ⟨n, hn⟩ := hb (X.l i) (X.lPrime i).out
  obtain ⟨M, hM⟩ := exists_pow_mul_isIntegral (X.O_l i) (u * ι Ω)
  refine ⟨M + n, fun Q hQ δ => exists_eq_of_isIntegral ?_⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth Q hQ
  obtain ⟨h1, h2⟩ := placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣
  have hf : ({q | π q⁻¹ = δ} : Set (PicO (condQ 𝔣 (belowSet Q)))).Finite := Set.toFinite _
  have hs : IsIntegral (X.O i) (∑ q ∈ hf.toFinset, ι (((X.l i : ℕ) : ℂ) ^ n * (T q / Ω))) :=
    IsIntegral.sum _ fun q _ => isIntegral_of_intAt (X.O_l i) ι (hn _ h1 h2 _ _ (hT q))
  refine (congrArg (IsIntegral (X.O i)) ?_).mpr (hM.mul hs)
  rw [map_mul, map_pow, map_natCast, hδ, finsum_mem_eq_finite_toFinset_sum _ hf, ← map_sum, ← Finset.mul_sum, ← Finset.sum_div,
    map_mul, map_pow, map_natCast, map_div₀]
  have : ι Ω ≠ 0 := (map_ne_zero ι).2 hΩ
  field_simp
  ring

variable (X)

/- English proof (translation)
Establish `key : ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ n : ℕ, X.NonzeroIndexPlace i → ∀ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s → ∀ Q, BlochKatoReduction.Gen.QOk X i Q → ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y = ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q la …`. Introduce `i lam`. Distinguish the cases in `hx : X.NonzeroIndexPlace i ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s`. Take `⟨hi, s, hs⟩` from `hx`. Take `⟨s, rfl⟩` from `Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)`.

Take `⟨ι, -, hι⟩` from `ht i hi`. Take `⟨n, hn⟩` from `exists_bound_at h (hι lam s hs)`. Conclude with `⟨n, fun _ _ _ => hn⟩`. Conclude with `⟨0, fun hi s hs => (hx ⟨hi, s, hs⟩).elim⟩`. Use `choose n hn using key`.

Use `⟨fun i => Finset.univ.sup (n i), fun i hi Q hQ lam s hs δ => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hn i lam hi s hs Q hQ δ`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := n i) (Finset.mem_univ lam))`. Use `⟨((X.l i : ℕ) : X.O i) ^ k * y, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, map_natCast, hy]`.

Use `show _ = _ ^ (Finset.univ.sup (n i)) * _`. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_gen_bound (h : ClassTermBound) (ht : IsToricElt X) : ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 := by
  classical
  have key : ∀ (i : X.Tw) (lam : X.abelian₂ i), ∃ n : ℕ, X.NonzeroIndexPlace i → ∀ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s → ∀ Q, BlochKatoReduction.Gen.QOk X i Q →
      ∀ δ, ∃ y : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) y =
        ((X.l i : ℕ) : FractionRing (X.O i)) ^ n * X.th i Q lam δ := by
    intro i lam
    by_cases hx : X.NonzeroIndexPlace i ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s
    · obtain ⟨hi, s, hs⟩ := hx
      obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
      obtain ⟨ι, -, hι⟩ := ht i hi
      obtain ⟨n, hn⟩ := exists_bound_at h (hι lam s hs)
      exact ⟨n, fun _ _ _ => hn⟩
    · exact ⟨0, fun hi s hs => (hx ⟨hi, s, hs⟩).elim⟩
  choose n hn using key
  refine ⟨fun i => Finset.univ.sup (n i), fun i hi Q hQ lam s hs δ => ?_⟩
  obtain ⟨y, hy⟩ := hn i lam hi s hs Q hQ δ
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n i) (Finset.mem_univ lam))
  refine ⟨((X.l i : ℕ) : X.O i) ^ k * y, ?_⟩
  rw [map_mul, map_pow, map_natCast, hy]
  show _ = _ ^ (Finset.univ.sup (n i)) * _
  rw [hk]
  ring

end Record

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ X ht => exists_gen_bound X h ht, fun D ht => exists_gen_bound D.ntw h ht⟩`.
-/
theorem bounded_denominators (h : ClassTermBound) :
    (∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), IsToricElt X →
      ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0) ∧
    ∀ D : D7, IsToricElt D.ntw → ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 :=
  ⟨fun _ _ X ht => exists_gen_bound X h ht, fun D ht => exists_gen_bound D.ntw h ht⟩

end GlobalTheory.ToricDenom
