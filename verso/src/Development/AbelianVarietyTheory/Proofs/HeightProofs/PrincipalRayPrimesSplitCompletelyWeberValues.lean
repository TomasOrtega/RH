import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrimesOneModNSplitCompletelyWeberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrimeStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberSplit
open scoped IntermediateField

namespace GlobalTheory.WeberSplitAny

/- English proof (translation)
Introduce `K _ _ h2 hd L hL n hn`. Establish `hn0 : (n : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `g2` using `g₂_ne_zero K h2 L hL hd`. Establish `g3` using `g₃_ne_zero K h2 L hL hd`. Establish `hD` using `g₂_cube_sub_g₃_sq_ne_zero L`.

Take `⟨hfin, halg, hperm⟩` from `GlobalTheory.T.weberValues_finite_algebraic_permuted L n (by omega) g2 g3`. Use `replace halg := halg (invariant_isAlgebraic K h2 L hL)`. Establish `hweb` using `GlobalTheory.T.weber_values_congruences_mod_degree_one_prime K h2 L hL`. Establish `hJw : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∈ weberSet L n` using `Or.inl rfl`. Establish `hJ0 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0` using `div_ne_zero (pow_ne_zero _ g2) hD`.

Establish `hJ1 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1 ≠ 0`. Rewrite using `[sub_ne_zero, Ne, div_eq_one_iff_eq hD]`. Introduce `h`. Conclude with `g3 (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination h / 27))`. Establish `hw : ∀ w ∈ weberSet L n, w = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∨ ∃ t, (n : ℂ) * t ∈ L.lattice ∧ t ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t`.

Introduce and unpack `w (h | ⟨z, hz, hz', e⟩)`. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨z / n, by rwa [mul_div_cancel₀ _ hn0], hz', e⟩`. Generalize the expression as in `L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = J at *`. Generalize the expression as in `L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = u at *`.

Generalize the expression as in `weberSet L n = T at *`. Use `hfin.to_subtype` as an intermediate fact. Establish `hfd : FiniteDimensional K (IntermediateField.adjoin K T)` using `IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral.tower_top`. Establish `hM : NumberField (IntermediateField.adjoin K T)` using `NumberField.of_module_finite K _`. Use `⟨hM, ?_⟩` and prove the remaining obligations.

Establish `hTM` using `IntermediateField.subset_adjoin K T`. Use `set M := IntermediateField.adjoin K T`. Establish `hext : ∀ (N : Type) [Field N] [Algebra K N] (f g : M →ₐ[K] N), (∀ x (hx : x ∈ T), f ⟨x, hTM hx⟩ = g ⟨x, hTM hx⟩) → f = g` using `fun N _ _ f g h => IntermediateField.adjoin_algHom_ext K h`. Use `clear_value M`. Take `⟨N, _, _, _, _, _, _, ι, hι⟩` from `exists_isGalois K M`.

Use `replace hι : ∀ x : M, ι (algebraMap M N x) = x := hι`. Establish `hιK : ∀ x : K, ι (algebraMap K N x) = x` using `fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K M N, hι]`. Both sides reduce to the same expression. Set `j : N` to `algebraMap M N ⟨J, hTM hJw⟩`.

Establish `hj : ι j = J` using `hι _`. Establish `hfin' : (ι ⁻¹' T).Finite` using `hfin.preimage ι.injective.injOn`. Take `⟨d, hd0, hdi⟩` from `exists_integral_multiples ℤ ℚ (hfin'.toFinset ∪ {j⁻¹, (j - 1)⁻¹} ∪ Finset.univ.image fun σ : N ≃ₐ[K] N => (σ j - j)⁻¹)`. Use `⟨(6 * n * d.natAbs).primeFactors, fun π p hp hpS hN hπ => ?_⟩` and prove the remaining obligations. Establish `hnd : ¬ p ∣ 6 * n * d.natAbs` using `fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, by positivity⟩)`.

Establish `hpn : ¬ p ∣ n` using `fun h => hnd ((h.mul_left _).mul_right _)`. Establish `hpd : ¬ (p : ℤ) ∣ d` using `fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)`. Establish `hp5 : 5 ≤ p`. Assume the negation of the conclusion as `h`. Establish `h6 : ¬ p ∣ 6` using `fun h => hnd ((h.mul_right _).mul_right _)`.

Use `hp.two_le` as an intermediate fact. Establish `: p < 5` using `by omega`. Use `interval_cases p`. Use `exacts [h6 (by norm_num), h6 (by norm_num), absurd hp (by norm_num)]`. Establish `hprime : (Ideal.span {π}).IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)`.

Establish `hbot : Ideal.span {π} ≠ ⊥` using `fun h => hp.ne_zero (by rw [← hN, h]; simp)`. Use `ncard_eq_of_tower K M N ⟨Ideal.span {π}, hprime, hbot⟩ ?_` and prove the remaining obligations. Introduce and unpack `σ ⟨P, hP, hPo, hσ⟩`. Simplify using `only [hN] at hσ hPo`. Take `⟨W, hW⟩` from `exists_valuationSubring ι P hP.ne_top`.

Establish `hover : ∀ x ∈ Ideal.span {π}, W.valuation ((x : K) : ℂ) < 1` using `fun x hx => by`. Establish `h` using `hW _ ((Ideal.mem_of_liesOver P (Ideal.span {π}) x).1 hx)`. Rewrite using `[← hιK]`. Conclude with `h`. Establish `hpW : W.valuation p < 1`.

Simplify `hover _ (Ideal.absNorm_mem (Ideal.span {π}))` using `[hN]`. Take `⟨-, hJp, hm⟩` from `hweb W π p hp hp5 hN (W.mem_nonunits_iff.2 (hover _ (Ideal.mem_span_singleton_self _)))`. Take `⟨hm1, hm2⟩` from `hm n hpn`. Simplify using `only [ValuationSubring.mem_nonunits_iff] at hJp hm1 hm2`. Establish `hc : ∀ x : N, ι x ∈ T → W.valuation (ι (σ x) - ι x ^ p) < 1` using `fun x hx => frob_congr ι σ W hp hpW (fun y => hW _ (hσ y)) hpd (hdi x (by simp [hx]))`.

Establish `hz : ∀ x : N, IsIntegral ℤ (d • x⁻¹) → W.valuation (ι x) < 1 → x = 0` using `fun x => eq_zero_of_valuation_lt_one ι W hp hpW hpd`. Establish `hσj : σ j = j`. Use `sub_eq_zero.1 (hz _ (hdi _ (by simp)) ?_)` and prove the remaining obligations. Use `Valuation.map_sub_lt _ (hc j (hj ▸ hJw)) hJp` as an intermediate fact. Rewrite using `[map_sub ι]`.

Rewrite `this`, the goal using `[hj]`. Use `this using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hm3` using `hm2 (fun h => hJ0 (by rw [← hj, hz j (hdi _ (by simp)) (hj ▸ h), map_zero])) (fun h => hJ1 (by`. Establish `e : ι (j - 1) = J - 1` using `by rw [map_sub, hj, map_one]`.

Rewrite using `[← e, hz (j - 1) (hdi _ (by simp)) (e ▸ h), map_zero]))`. Establish `: Countable N` using `Finsupp.Countable.of_moduleFinite (R := ℚ)`. Take `⟨τ, hτ⟩` from `GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N ι (ι.comp σ.toRingEquiv.toRingHom)`. Establish `hτ' : ∀ x, τ (ι x) = ι (σ x)` using `hτ`. Establish `key : (σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K M N) = IsScalarTower.toAlgHom K M N`.

Use `hext N _ _ fun w hwT => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (algebraMap M N ⟨w, hTM hwT⟩) = algebraMap M N ⟨w, hTM hwT⟩`. Break down `hw w hwT with rfl | ⟨t, ht, ht', rfl⟩` into its components or cases. Conclude with `hσj`. Use `set x := algebraMap M N ⟨_, hTM hwT⟩`.

Establish `hx : ι x = u * L.weierstrassP t` using `hι _`. Take `⟨s, hs, hs', e⟩` from `hperm τ (by rw [← hj, hτ', hσj]) t ht ht'`. Establish `h1` using `hc x (hx ▸ hwT)`. Rewrite `h1` using `[← hτ', hx, e]`. Establish `h3` using `(hm1 t ht ht').2`.

Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hπ`. Take `⟨a, ha⟩` from `(hL _).1 ht`. Establish `e1 : ((π : K) : ℂ) * t = t + ((c * a : 𝓞 K) : K)`. Establish `: ((c : K) : ℂ) * n = ((π : K) : ℂ) - 1`. Simplify using `using congrArg (fun y : 𝓞 K => ((y : K) : ℂ)) hc`.

Use `push_cast`. Rewrite using `[ha]`. Take the linear combination `-t * this`. Rewrite `h3` using `[e1, L.weierstrassP_add_coe t ⟨_, (hL _).2 ⟨_, rfl⟩⟩]`. Establish `h4` using `Valuation.map_sub_lt _ h3 h1`.

Rewrite `h4` using `[sub_sub_sub_cancel_right]`. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[← hτ', hx, e]`. Use `congr 1`. Break down `hm3 t s ht ht' hs hs' h4 with h | h` into its components or cases.

Rewrite using `[← L.weierstrassP_add_coe s ⟨_, h⟩]`. Simplify using the standard rewrite rules. Rewrite using `[← L.weierstrassP_neg s, ← L.weierstrassP_add_coe (-s) ⟨_, h⟩]`. Simplify using the standard rewrite rules. Conclude with `fun x => DFunLike.congr_fun key x`.
-/
theorem splits_completely_of_three_le : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n))) (S : Finset ℕ), ∀ (π : 𝓞 K) (p : ℕ), p.Prime → p ∉ S → Ideal.absNorm (Ideal.span {π}) = p → π - 1 ∈ Ideal.span {(n : 𝓞 K)} → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K (weberSet L n))) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K (weberSet L n)))) = Ideal.span {π}}.ncard = Module.finrank K (IntermediateField.adjoin K (weberSet L n)) := by
  classical
  intro K _ _ h2 hd L hL n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have g2 := g₂_ne_zero K h2 L hL hd
  have g3 := g₃_ne_zero K h2 L hL hd
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨hfin, halg, hperm⟩ := GlobalTheory.T.weberValues_finite_algebraic_permuted L n (by omega) g2 g3
  replace halg := halg (invariant_isAlgebraic K h2 L hL)
  have hweb := GlobalTheory.T.weber_values_congruences_mod_degree_one_prime K h2 L hL
  have hJw : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∈ weberSet L n := Or.inl rfl
  have hJ0 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0 := div_ne_zero (pow_ne_zero _ g2) hD
  have hJ1 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_one_iff_eq hD]
    intro h
    exact g3 (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination h / 27))
  have hw : ∀ w ∈ weberSet L n, w = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∨ ∃ t, (n : ℂ) * t ∈ L.lattice ∧
      t ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t := by
    rintro w (h | ⟨z, hz, hz', e⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z / n, by rwa [mul_div_cancel₀ _ hn0], hz', e⟩
  generalize L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = J at *
  generalize L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = u at *
  generalize weberSet L n = T at *
  have := hfin.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral.tower_top
  have hM : NumberField (IntermediateField.adjoin K T) := NumberField.of_module_finite K _
  refine ⟨hM, ?_⟩
  have hTM := IntermediateField.subset_adjoin K T
  set M := IntermediateField.adjoin K T
  have hext : ∀ (N : Type) [Field N] [Algebra K N] (f g : M →ₐ[K] N),
      (∀ x (hx : x ∈ T), f ⟨x, hTM hx⟩ = g ⟨x, hTM hx⟩) → f = g :=
    fun N _ _ f g h => IntermediateField.adjoin_algHom_ext K h
  clear_value M
  obtain ⟨N, _, _, _, _, _, _, ι, hι⟩ := exists_isGalois K M
  replace hι : ∀ x : M, ι (algebraMap M N x) = x := hι
  have hιK : ∀ x : K, ι (algebraMap K N x) = x := fun x => by
    rw [IsScalarTower.algebraMap_apply K M N, hι]; rfl
  let j : N := algebraMap M N ⟨J, hTM hJw⟩
  have hj : ι j = J := hι _
  have hfin' : (ι ⁻¹' T).Finite := hfin.preimage ι.injective.injOn
  obtain ⟨d, hd0, hdi⟩ := exists_integral_multiples ℤ ℚ (hfin'.toFinset ∪ {j⁻¹, (j - 1)⁻¹} ∪
    Finset.univ.image fun σ : N ≃ₐ[K] N => (σ j - j)⁻¹)
  refine ⟨(6 * n * d.natAbs).primeFactors, fun π p hp hpS hN hπ => ?_⟩
  have hnd : ¬ p ∣ 6 * n * d.natAbs := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, by positivity⟩)
  have hpn : ¬ p ∣ n := fun h => hnd ((h.mul_left _).mul_right _)
  have hpd : ¬ (p : ℤ) ∣ d := fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)
  have hp5 : 5 ≤ p := by
    by_contra h
    have h6 : ¬ p ∣ 6 := fun h => hnd ((h.mul_right _).mul_right _)
    have := hp.two_le
    have : p < 5 := by omega
    interval_cases p
    exacts [h6 (by norm_num), h6 (by norm_num), absurd hp (by norm_num)]
  have hprime : (Ideal.span {π}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  have hbot : Ideal.span {π} ≠ ⊥ := fun h => hp.ne_zero (by rw [← hN, h]; simp)
  refine ncard_eq_of_tower K M N ⟨Ideal.span {π}, hprime, hbot⟩ ?_
  rintro σ ⟨P, hP, hPo, hσ⟩
  simp only [hN] at hσ hPo
  obtain ⟨W, hW⟩ := exists_valuationSubring ι P hP.ne_top
  have hover : ∀ x ∈ Ideal.span {π}, W.valuation ((x : K) : ℂ) < 1 := fun x hx => by
    have h := hW _ ((Ideal.mem_of_liesOver P (Ideal.span {π}) x).1 hx)
    rw [← hιK]
    exact h
  have hpW : W.valuation p < 1 := by
    simpa [hN] using hover _ (Ideal.absNorm_mem (Ideal.span {π}))
  obtain ⟨-, hJp, hm⟩ := hweb W π p hp hp5 hN (W.mem_nonunits_iff.2 (hover _ (Ideal.mem_span_singleton_self _)))
  obtain ⟨hm1, hm2⟩ := hm n hpn
  simp only [ValuationSubring.mem_nonunits_iff] at hJp hm1 hm2
  have hc : ∀ x : N, ι x ∈ T → W.valuation (ι (σ x) - ι x ^ p) < 1 := fun x hx =>
    frob_congr ι σ W hp hpW (fun y => hW _ (hσ y)) hpd (hdi x (by simp [hx]))
  have hz : ∀ x : N, IsIntegral ℤ (d • x⁻¹) → W.valuation (ι x) < 1 → x = 0 := fun x =>
    eq_zero_of_valuation_lt_one ι W hp hpW hpd
  have hσj : σ j = j := by
    refine sub_eq_zero.1 (hz _ (hdi _ (by simp)) ?_)
    have := Valuation.map_sub_lt _ (hc j (hj ▸ hJw)) hJp
    rw [map_sub ι]
    rw [hj] at this ⊢
    convert this using 2
    ring
  have hm3 := hm2 (fun h => hJ0 (by rw [← hj, hz j (hdi _ (by simp)) (hj ▸ h), map_zero]))
    (fun h => hJ1 (by
      have e : ι (j - 1) = J - 1 := by rw [map_sub, hj, map_one]
      rw [← e, hz (j - 1) (hdi _ (by simp)) (e ▸ h), map_zero]))
  have : Countable N := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N ι (ι.comp σ.toRingEquiv.toRingHom)
  have hτ' : ∀ x, τ (ι x) = ι (σ x) := hτ
  have key : (σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K M N) = IsScalarTower.toAlgHom K M N := by
    refine hext N _ _ fun w hwT => ?_
    change σ (algebraMap M N ⟨w, hTM hwT⟩) = algebraMap M N ⟨w, hTM hwT⟩
    rcases hw w hwT with rfl | ⟨t, ht, ht', rfl⟩
    · exact hσj
    · set x := algebraMap M N ⟨_, hTM hwT⟩
      have hx : ι x = u * L.weierstrassP t := hι _
      obtain ⟨s, hs, hs', e⟩ := hperm τ (by rw [← hj, hτ', hσj]) t ht ht'
      have h1 := hc x (hx ▸ hwT)
      rw [← hτ', hx, e] at h1
      have h3 := (hm1 t ht ht').2
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hπ
      obtain ⟨a, ha⟩ := (hL _).1 ht
      have e1 : ((π : K) : ℂ) * t = t + ((c * a : 𝓞 K) : K) := by
        have : ((c : K) : ℂ) * n = ((π : K) : ℂ) - 1 := by
          simpa using congrArg (fun y : 𝓞 K => ((y : K) : ℂ)) hc
        push_cast
        rw [ha]
        linear_combination -t * this
      rw [e1, L.weierstrassP_add_coe t ⟨_, (hL _).2 ⟨_, rfl⟩⟩] at h3
      have h4 := Valuation.map_sub_lt _ h3 h1
      rw [sub_sub_sub_cancel_right] at h4
      apply ι.injective
      rw [← hτ', hx, e]
      congr 1
      rcases hm3 t s ht ht' hs hs' h4 with h | h
      · rw [← L.weierstrassP_add_coe s ⟨_, h⟩]
        simp
      · rw [← L.weierstrassP_neg s, ← L.weierstrassP_add_coe (-s) ⟨_, h⟩]
        simp
  exact fun x => DFunLike.congr_fun key x

end GlobalTheory.WeberSplitAny
