import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
import Development.AutomorphicArithmetic.WhittakerHecke.InertOrSplitOfGoodDeltaRat
import Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
import Development.AutomorphicArithmetic.WhittakerHecke.IdeleOfNatMulAndPrimePow
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsMultiplicativeOfPrimePowerValues
import Development.AutomorphicArithmetic.WhittakerHecke.KAtDiagIdeleOfNatMulRotationOfNotDvd
import Development.AutomorphicArithmetic.WhittakerHecke.EqConvolutionSquareIndicatorOfEulerFactors
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtInertPlace
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtSplitPlace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem aE_mul' {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : aE (x * y) = aE x * aE y := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Introduce `E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG a hIs`. Take `⟨hpr, hex, hinj, hbad⟩` from `UpperTheory.heightOneSpectrum_rat_correspond_primes`. Take `⟨pmul, ppow⟩` from `UpperTheory.ideleOfNat_mul_and_prime_pow`. Establish `pin1 : pin 1 = 1`. Use `pmul 1 1 one_pos one_pos` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Conclude with `mul_eq_left.1 this.symm`. Establish `pack : ∀ v : H.P ℚ, ¬ Bad N v → ∃ m : ℕ → ℂ, m 0 = 1 ∧ (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧ ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fu …` using `fun v hv => by`. Break down `UpperTheory.inert_or_split_of_good_delta_rat E D v (hG.pl v hv) with ⟨w, hw, hI⟩ | ⟨w, w', hne, hw, hw', hs, hs', hall⟩` into its components or cases. Conclude with `UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w hw hI`.

Conclude with `UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w w' hne hw hw' hs hs' hall`. Use `choose! M hM0 hM1 hM2 using pack`. Take `⟨μ, hμ1, hμm, hμp⟩` from `UpperTheory.exists_multiplicative_of_prime_power_values (fun v k => if Bad N v then 1 else M v k) (fun v => by`. Distinguish the cases in `h : Bad N v`. Simplify using `[h]`.

Simplify using `[h, hM0 v h])`. Establish `hpN : ∀ v : H.P ℚ, ¬ normV v ∣ N → ¬ Bad N v` using `fun v h hb => h ((hbad N v).1 hb)`. Establish `hμv : ∀ (v : H.P ℚ) (k : ℕ), ¬ Bad N v → μ (normV v ^ k) = M v k` using `fun v k h => by`. Use `hμp v k` as an intermediate fact. Simplify `this` using `[h]`.

Use `⟨μ, ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `hn hc r t hr`.

Distinguish the cases in `h1 : n = 1`. Substitute `h1` using the available equality. Rewrite using `[pin1, mul_one, hμ1, one_mul]`. Establish `hp : n.minFac.Prime` using `Nat.minFac_prime h1`. Take `⟨k, m, hnd, hnm⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' n.minFac hp.ne_one`.

Take `⟨v, hv⟩` from `hex _ hp`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`. Rewrite `hnm` using `[pow_zero, one_mul]`. Conclude with `hnd (hnm ▸ Nat.minFac_dvd n)`.

Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by`. Introduce and unpack `rfl`. Simplify using `at hnm`. Use the proof step `omega)`. Establish `hmlt : m < n`.

Establish `h2 : 2 ≤ n.minFac ^ k`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Establish `hmc : m.Coprime N` using `Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hnm.symm) hc`. Establish `hvb : ¬ Bad N v` using `hpN v fun h => Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n) (hv ▸ h) hc`.

Establish `hcop : (normV v ^ k).Coprime m` using `Nat.Coprime.pow_left k (by rw [hv]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)`. Establish `hpin : pin n = pv v ^ k * pin m`. Rewrite using `[hnm, ← hv, pmul _ _ (pow_pos (hpr v).pos k) hm0, ppow]`. Establish `hg : em E (aE (iy r * pin n) * rot t) = em E (aE (pv v ^ k)) * em E (aE (iy r * pin m) * rot t)`. Rewrite using `[hpin, mul_left_comm, aE_mul', map_mul, map_mul, map_mul, mul_assoc]`.

Establish `hnv : n = normV v ^ k * m` using `by rw [hv]; exact hnm`. Rewrite using `[hg, hM1 v hvb k _ (fun w hw => UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd E v m r t hm0 (by rw [hv]; exact hnd) w hw), ih m hmlt hm0 hmc r t hr, ← mul_assoc, ← hμv v k hvb, ← hμm _ _ (pow_pos (hpr v).pos k) hm0 hcop, ← hnv]`. Introduce and unpack `⟨r, t, hr, hne⟩ n hn`. Use `UpperTheory.eq_convolution_squareIndicator_of_euler_factors N a (bN N χ μ) hG.pos hIs.one hIs.mul hIs.bad ?_ ?_ ?_ ?_ n hn` and prove the remaining obligations. Simplify using `[bN, pin1, hμ1]`.

Introduce `x y hx hy hxy`. Simplify using `only [bN, Nat.coprime_mul_iff_left]`. Distinguish the cases in `h1 : x.Coprime N`. Distinguish the cases in `h2 : y.Coprime N`. Rewrite using `[if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, pmul x y hx hy, hμm x y hx hy hxy, map_mul, Units.val_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg fun h => h2 h.2, if_neg h2, mul_zero]`. Rewrite using `[if_neg fun h => h1 h.1, if_neg h1, zero_mul]`. Introduce `x hx`.

Simplify using `only [bN]`. Rewrite using `[if_neg hx]`. Introduce `p hp hpn`. Take `⟨v, rfl⟩` from `hex p hp`. Establish `hvb` using `hpN v hpn`.

Rewrite using `[hM2 v hvb ⟨_, hne⟩]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Establish `hc : (normV v ^ k).Coprime N` using `Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)`. Simplify using `only [bN, if_pos hc]`.

Rewrite using `[ppow, map_pow, Units.val_pow_eq_pow_val, hμv v k hvb]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∃ μ : ℕ → ℂ,
        (∀ n, 0 < n → n.Coprime N → ∀ r t : ℝ, r ≠ 0 →
          Wo D φ (em E (aE (iy r * pin n) * rot t)) = μ n * Wo D φ (em E (aE (iy r) * rot t))) ∧
        ((∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0) → ∀ n, n ≠ 0 → a n = LSeries.convolution (bN N χ μ) (sqN N) n) := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  obtain ⟨hpr, hex, hinj, hbad⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  obtain ⟨pmul, ppow⟩ := UpperTheory.ideleOfNat_mul_and_prime_pow
  have pin1 : pin 1 = 1 := by
    have := pmul 1 1 one_pos one_pos
    rw [one_mul] at this
    exact mul_eq_left.1 this.symm
  have pack : ∀ v : H.P ℚ, ¬ Bad N v → ∃ m : ℕ → ℂ, m 0 = 1 ∧ (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧ ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := fun v hv => by
    rcases UpperTheory.inert_or_split_of_good_delta_rat E D v (hG.pl v hv) with ⟨w, hw, hI⟩ | ⟨w, w', hne, hw, hw', hs, hs', hall⟩
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w hw hI
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w w' hne hw hw' hs hs' hall
  choose! M hM0 hM1 hM2 using pack
  obtain ⟨μ, hμ1, hμm, hμp⟩ := UpperTheory.exists_multiplicative_of_prime_power_values (fun v k => if Bad N v then 1 else M v k) (fun v => by
    by_cases h : Bad N v
    · simp [h]
    · simp [h, hM0 v h])
  have hpN : ∀ v : H.P ℚ, ¬ normV v ∣ N → ¬ Bad N v := fun v h hb => h ((hbad N v).1 hb)
  have hμv : ∀ (v : H.P ℚ) (k : ℕ), ¬ Bad N v → μ (normV v ^ k) = M v k := fun v k h => by
    have := hμp v k
    simpa [h] using this
  refine ⟨μ, ?_, ?_⟩
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hc r t hr
      by_cases h1 : n = 1
      · subst h1
        rw [pin1, mul_one, hμ1, one_mul]
      have hp : n.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨k, m, hnd, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' n.minFac hp.ne_one
      obtain ⟨v, hv⟩ := hex _ hp
      have hk : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hnd (hnm ▸ Nat.minFac_dvd n)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by
        rintro rfl
        simp at hnm
        omega)
      have hmlt : m < n := by
        have h2 : 2 ≤ n.minFac ^ k := by
          calc 2 ≤ n.minFac := hp.two_le
            _ = n.minFac ^ 1 := (pow_one _).symm
            _ ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hk)
        nlinarith
      have hmc : m.Coprime N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hnm.symm) hc
      have hvb : ¬ Bad N v := hpN v fun h =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n) (hv ▸ h) hc
      have hcop : (normV v ^ k).Coprime m :=
        Nat.Coprime.pow_left k (by rw [hv]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
      have hpin : pin n = pv v ^ k * pin m := by
        rw [hnm, ← hv, pmul _ _ (pow_pos (hpr v).pos k) hm0, ppow]
      have hg : em E (aE (iy r * pin n) * rot t) = em E (aE (pv v ^ k)) * em E (aE (iy r * pin m) * rot t) := by
        rw [hpin, mul_left_comm, aE_mul', map_mul, map_mul, map_mul, mul_assoc]
      have hnv : n = normV v ^ k * m := by rw [hv]; exact hnm
      rw [hg, hM1 v hvb k _ (fun w hw => UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd E v m r t hm0 (by rw [hv]; exact hnd) w hw), ih m hmlt hm0 hmc r t hr,
        ← mul_assoc, ← hμv v k hvb, ← hμm _ _ (pow_pos (hpr v).pos k) hm0 hcop, ← hnv]
  · rintro ⟨r, t, hr, hne⟩ n hn
    refine UpperTheory.eq_convolution_squareIndicator_of_euler_factors N a (bN N χ μ) hG.pos hIs.one hIs.mul hIs.bad ?_ ?_ ?_ ?_ n hn
    · simp [bN, pin1, hμ1]
    · intro x y hx hy hxy
      simp only [bN, Nat.coprime_mul_iff_left]
      by_cases h1 : x.Coprime N
      · by_cases h2 : y.Coprime N
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, pmul x y hx hy, hμm x y hx hy hxy, map_mul, Units.val_mul]
          push_cast
          ring
        · rw [if_neg fun h => h2 h.2, if_neg h2, mul_zero]
      · rw [if_neg fun h => h1 h.1, if_neg h1, zero_mul]
    · intro x hx
      simp only [bN]
      rw [if_neg hx]
    · intro p hp hpn
      obtain ⟨v, rfl⟩ := hex p hp
      have hvb := hpN v hpn
      rw [hM2 v hvb ⟨_, hne⟩]
      congr 1
      funext k
      have hc : (normV v ^ k).Coprime N := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      simp only [bN, if_pos hc]
      rw [ppow, map_pow, Units.val_pow_eq_pow_val, hμv v k hvb]
      rfl
