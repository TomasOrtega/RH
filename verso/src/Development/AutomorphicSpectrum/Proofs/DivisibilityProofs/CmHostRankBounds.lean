import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuadraticFieldDiscPrimeThreeModFour

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top.HostNumbers

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `h` using `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq`. Move the coercions through the operations in `at h`. Conclude with `h`.
-/
theorem rt_sq (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have h := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
  push_cast at h
  exact h

/- English proof (translation)
Establish `h` using `H.d_mod`. Use linear arithmetic over natural numbers and integers.
-/
theorem seven_le_d (H : Host E) : 7 ≤ H.d := by
  have h := H.d_mod
  omega

/- English proof (translation)
Establish `hm' : (0:ℝ) < m` using `by exact_mod_cast hm`. Establish `hb : (1:ℝ) + m * (1 / m) ≤ (1 + 1 / m) ^ m` using `one_add_mul_le_pow (by have : (0:ℝ) ≤ 1 / m := by positivity linarith) m`. Establish `h1 : (1:ℝ) + m * (1 / m) = 2` using `by field_simp; ring`. Establish `hR : (2:ℝ) * (m:ℝ) ^ m ≤ ((m:ℝ) + 1) ^ m`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hR` after adjusting the coercions.
-/
private theorem two_mul_pow_self_le_succ_pow (m : ℕ) (hm : 1 ≤ m) : 2 * m ^ m ≤ (m + 1) ^ m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hb : (1:ℝ) + m * (1 / m) ≤ (1 + 1 / m) ^ m :=
    one_add_mul_le_pow (by have : (0:ℝ) ≤ 1 / m := by positivity
                           linarith) m
  have h1 : (1:ℝ) + m * (1 / m) = 2 := by field_simp; ring
  have hR : (2:ℝ) * (m:ℝ) ^ m ≤ ((m:ℝ) + 1) ^ m := by
    calc (2:ℝ) * (m:ℝ) ^ m = (1 + m * (1 / m)) * (m:ℝ) ^ m := by rw [h1]
      _ ≤ (1 + 1 / m) ^ m * (m:ℝ) ^ m := by gcongr
      _ = ((1 + 1 / m) * m) ^ m := by rw [mul_pow]
      _ = ((m:ℝ) + 1) ^ m := by congr 1; field_simp
  exact_mod_cast hR

/- English proof (translation)
Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => norm_num`. Consider the case `succ k hk ih`. Establish `h1` using `two_mul_pow_self_le_succ_pow k hk`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Nat.factorial_succ, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 2 * (k+1) * (2 * k ^ k) := Nat.mul_le_mul_left _ ih`. Use `_ ≤ 2 * (k+1) * (k+1) ^ k := Nat.mul_le_mul_left _ h1`. Use `_ = 2 * (k+1) ^ (k+1) := by ring`.
-/
private theorem two_pow_mul_factorial_le_two_mul_pow_self (m : ℕ) (hm : 1 ≤ m) : 2 ^ m * m.factorial ≤ 2 * m ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 := two_mul_pow_self_le_succ_pow k hk
    calc 2 ^ (k+1) * (k+1).factorial = 2 * (k+1) * (2 ^ k * k.factorial) := by
          rw [Nat.factorial_succ, pow_succ]; ring
      _ ≤ 2 * (k+1) * (2 * k ^ k) := Nat.mul_le_mul_left _ ih
      _ ≤ 2 * (k+1) * (k+1) ^ k := Nat.mul_le_mul_left _ h1
      _ = 2 * (k+1) ^ (k+1) := by ring

/- English proof (translation)
Establish `h` using `two_pow_mul_factorial_le_two_mul_pow_self m (by omega)`. Establish `hsq : (2 ^ m * m.factorial) ^ 2 ≤ (2 * m ^ m) ^ 2` using `Nat.pow_le_pow_left h 2`. Establish `h4' : 4 ≤ 2 ^ m`. Combine the equalities or inequalities in the displayed calculation. Establish `h4 : 4 * 2 ^ m ≤ 2 ^ m * 2 ^ m` using `Nat.mul_le_mul_right _ h4'`.

Establish `h5 : 4 * (2 ^ m * m.factorial ^ 2) ≤ 4 * m ^ (2 * m)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.le_of_mul_le_mul_left h5 (by norm_num)`.
-/
private theorem two_pow_mul_factorial_sq_le_pow_two_mul (m : ℕ) (hm : 2 ≤ m) :
    2 ^ m * m.factorial ^ 2 ≤ m ^ (2 * m) := by
  have h := two_pow_mul_factorial_le_two_mul_pow_self m (by omega)
  have hsq : (2 ^ m * m.factorial) ^ 2 ≤ (2 * m ^ m) ^ 2 := Nat.pow_le_pow_left h 2
  have h4' : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h4 : 4 * 2 ^ m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_right _ h4'
  have h5 : 4 * (2 ^ m * m.factorial ^ 2) ≤ 4 * m ^ (2 * m) := by
    calc 4 * (2 ^ m * m.factorial ^ 2) = (4 * 2 ^ m) * m.factorial ^ 2 := by ring
      _ ≤ (2 ^ m * 2 ^ m) * m.factorial ^ 2 := Nat.mul_le_mul_right _ h4
      _ = (2 ^ m * m.factorial) ^ 2 := by ring
      _ ≤ (2 * m ^ m) ^ 2 := hsq
      _ = 4 * m ^ (2 * m) := by ring
  exact Nat.le_of_mul_le_mul_left h5 (by norm_num)

/- English proof (translation)
Set `F` to `maximalRealSubfield E`. Establish `hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤`. Use `letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 E))`. Use `haveI := H.unram`. Assume the negation of the conclusion as `hne`.

Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Use `haveI := hP.isPrime`. Establish `hdvd : P ∣ differentIdeal (𝓞 F) (𝓞 E)` using `Ideal.dvd_iff_le.mpr hle`. Establish `hun : Algebra.IsUnramifiedAt (𝓞 F) P` using `Algebra.FormallyUnramified.comp (𝓞 F) (𝓞 E) (Localization.AtPrime P)`. Conclude with `((not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).mpr hun) hdvd`.

Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Establish `htow : (discr E).natAbs = (discr F).natAbs ^ 2`. Rewrite using `[NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E), hdiff, ← Ideal.one_eq_top, map_one, one_mul, h2]`. Establish `hfr : Module.finrank ℚ E = 2 * Module.finrank ℚ F`. Rewrite using `[← Module.finrank_mul_finrank ℚ F E, h2, mul_comm]`.

Establish `hFpos : 0 < Module.finrank ℚ F` using `Module.finrank_pos`. Break down `Nat.lt_or_ge (Module.finrank ℚ F) 2 with hm | hm` into its components or cases. It suffices to derive a contradiction. Establish `hm1 : Module.finrank ℚ F = 1` using `by omega`. Establish `hE : 2 < |discr E|` using `NumberField.abs_discr_gt_two (by rw [hfr]; omega)`.

Establish `hinj : Function.Injective (Algebra.ofId ℚ F)` using `(Algebra.ofId ℚ F).toRingHom.injective`. Establish `hsurj : Function.Surjective (Algebra.ofId ℚ F)` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (Algebra.ofId ℚ F).toLinearMap) (by rw [Module.finrank_self, hm1])).mp hinj`. Establish `hF : discr F = 1`. Rewrite using `[← NumberField.discr_eq_discr_of_algEquiv ℚ (AlgEquiv.ofBijective (Algebra.ofId ℚ F) ⟨hinj, hsurj⟩), NumberField.discr_rat]`. Rewrite `htow` using `[hF]`.

Establish `h1 : (discr E).natAbs = 1` using `by simpa using htow`. Rewrite `hE` using `[Int.abs_eq_natAbs, h1]`. Evaluate the numerical expressions using `at hE`. Establish `hF` using `NumberField.abs_discr_ge' F`. Rewrite `hF` using `[NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, pow_zero, one_mul]`.

Establish `key` using `two_pow_mul_factorial_sq_le_pow_two_mul _ hm`. Establish `hR : (2:ℝ) ^ Module.finrank ℚ F ≤ (((discr F).natAbs : ℤ) : ℝ)`. Rewrite using `[← Int.abs_eq_natAbs]`. Use `le_trans ?_ hF` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (by positivity)]`.

Conclude with `key` after adjusting the coercions. Establish `hN : 2 ^ Module.finrank ℚ F ≤ (discr F).natAbs` using `by exact_mod_cast hR`. Rewrite using `[htow, hfr, pow_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, ← pow_mul, mul_comm]`.

Use `_ ≤ (discr F).natAbs ^ 2 := Nat.pow_le_pow_left hN 2`.
-/
theorem two_pow_le_host (H : Host E) : 2 ^ Module.finrank ℚ E ≤ (discr E).natAbs := by
  let F := maximalRealSubfield E
  have hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 E))
    haveI := H.unram
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hP.isPrime
    have hdvd : P ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
    have hun : Algebra.IsUnramifiedAt (𝓞 F) P :=
      Algebra.FormallyUnramified.comp (𝓞 F) (𝓞 E) (Localization.AtPrime P)
    exact ((not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).mpr hun) hdvd
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  have htow : (discr E).natAbs = (discr F).natAbs ^ 2 := by
    rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E),
      hdiff, ← Ideal.one_eq_top, map_one, one_mul, h2]
  have hfr : Module.finrank ℚ E = 2 * Module.finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, h2, mul_comm]
  have hFpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  rcases Nat.lt_or_ge (Module.finrank ℚ F) 2 with hm | hm
  · exfalso
    have hm1 : Module.finrank ℚ F = 1 := by omega
    have hE : 2 < |discr E| := NumberField.abs_discr_gt_two (by rw [hfr]; omega)
    have hinj : Function.Injective (Algebra.ofId ℚ F) := (Algebra.ofId ℚ F).toRingHom.injective
    have hsurj : Function.Surjective (Algebra.ofId ℚ F) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (Algebra.ofId ℚ F).toLinearMap) (by rw [Module.finrank_self, hm1])).mp hinj
    have hF : discr F = 1 := by
      rw [← NumberField.discr_eq_discr_of_algEquiv ℚ (AlgEquiv.ofBijective (Algebra.ofId ℚ F) ⟨hinj, hsurj⟩),
        NumberField.discr_rat]
    rw [hF] at htow
    have h1 : (discr E).natAbs = 1 := by simpa using htow
    rw [Int.abs_eq_natAbs, h1] at hE
    norm_num at hE
  · have hF := NumberField.abs_discr_ge' F
    rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, pow_zero, one_mul] at hF
    have key := two_pow_mul_factorial_sq_le_pow_two_mul _ hm
    have hR : (2:ℝ) ^ Module.finrank ℚ F ≤ (((discr F).natAbs : ℤ) : ℝ) := by
      rw [← Int.abs_eq_natAbs]
      refine le_trans ?_ hF
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast key
    have hN : 2 ^ Module.finrank ℚ F ≤ (discr F).natAbs := by exact_mod_cast hR
    rw [htow, hfr, pow_mul]
    calc (2 ^ 2) ^ Module.finrank ℚ F = (2 ^ Module.finrank ℚ F) ^ 2 := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (discr F).natAbs ^ 2 := Nat.pow_le_pow_left hN 2

/- English proof (translation)
Establish `h` using `two_pow_le_host H`. Establish `hn : (Module.finrank ℚ E : ℝ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℚ) (M := E)).ne'` after adjusting the coercions. Establish `h' : ((2:ℝ) ^ Module.finrank ℚ E) ≤ |((discr E : ℤ) : ℝ)|`. Rewrite using `[← Int.cast_abs, Int.abs_eq_natAbs]`.

Conclude with `h` after adjusting the coercions. Unfold `hostRd`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hn, Real.rpow_one]`. Use `_ ≤ _ := Real.rpow_le_rpow (by positivity) h' (by positivity)`.
-/
theorem two_le_hostRd (H : Host E) : 2 ≤ hostRd E := by
  have h := two_pow_le_host H
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have h' : ((2:ℝ) ^ Module.finrank ℚ E) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h
  unfold hostRd
  calc (2:ℝ) = ((2:ℝ) ^ Module.finrank ℚ E) ^ (1 / (Module.finrank ℚ E : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hn, Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) h' (by positivity)

/- English proof (translation)
Establish `h` using `H.sqrt_neg_disc_sq`. Rewrite `h` using `[pow_two]`. Establish `hd : (7:ℝ) ≤ H.d` using `by exact_mod_cast seven_le_d H`. Establish `hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d:ℝ)`. Establish `h1` using `congrArg Complex.re h`.

Simplify using `only [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h1`. Conclude with `h1`. Establish `him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0`. Establish `h1` using `congrArg Complex.im h`. Simplify using `only [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h1`.

Conclude with `h1`. Establish `h1 : H.rt0.re * H.rt0.im = 0` using `by linear_combination (1/2 : ℝ) * him`. Establish `h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0`. Take the linear combination `(H.rt0.re * H.rt0.re) * hre + (H.rt0.re * H.rt0.im) * h1`. Establish `h3 : H.rt0.re * H.rt0.re = 0`.

Break down `mul_eq_zero.mp h2 with h4 | h4` into its components or cases. Conclude with `h4`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Establish `ha : H.rt0.re = 0` using `mul_self_eq_zero.mp h3`. Apply `Complex.ext` to reduce the goal to its premises.

Simplify using `only [Complex.conj_re, Complex.neg_re, ha, neg_zero]`. Simplify using `only [Complex.conj_im, Complex.neg_im]`.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  rw [pow_two] at h
  have hd : (7:ℝ) ≤ H.d := by exact_mod_cast seven_le_d H
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d:ℝ) := by
    have h1 := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h1
    exact h1
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have h1 := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h1
    exact h1
  have h1 : H.rt0.re * H.rt0.im = 0 := by linear_combination (1/2 : ℝ) * him
  have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by
    linear_combination (H.rt0.re * H.rt0.re) * hre + (H.rt0.re * H.rt0.im) * h1
  have h3 : H.rt0.re * H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact h4
    · nlinarith [mul_self_nonneg H.rt0.re]
  have ha : H.rt0.re = 0 := mul_self_eq_zero.mp h3
  apply Complex.ext
  · simp only [Complex.conj_re, Complex.neg_re, ha, neg_zero]
  · simp only [Complex.conj_im, Complex.neg_im]

/- English proof (translation)
Introduce `h`. Establish `h2` using `H.sqrt_neg_disc_sq`. Rewrite `h2` using `[h]`. Establish `h3 : (H.d : ℂ) = 0` using `by linear_combination h2`. Establish `h4 : H.d = 0` using `by exact_mod_cast h3`.

Use `seven_le_d H` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have h3 : (H.d : ℂ) = 0 := by linear_combination h2
  have h4 : H.d = 0 := by exact_mod_cast h3
  have := seven_le_d H
  omega

/- English proof (translation)
Establish `h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ)`. Rewrite using `[← map_pow, rt_sq H, map_neg, map_natCast]`. Establish `h2` using `H.sqrt_neg_disc_sq`. Establish `h3 : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0`. Take the linear combination `h1 - h2`.

Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.mp h)`. Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`.
-/
theorem emb_rt (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, rt_sq H, map_neg, map_natCast]
  have h2 := H.sqrt_neg_disc_sq
  have h3 : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

def conjEquiv (H : Host E) :
    {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} where
  toFun τ := ⟨ComplexEmbedding.conjugate τ.1, by
    rw [ComplexEmbedding.conjugate_coe_eq, τ.2, rt0_conj_neg_ne_zero]
    intro h
    exact rt0_ne_zero H (self_eq_neg.1 h.symm)⟩
  invFun τ := ⟨ComplexEmbedding.conjugate τ.1, by
    rw [ComplexEmbedding.conjugate_coe_eq, (emb_rt H τ.1).resolve_left τ.2, map_neg, rt0_conj_neg_ne_zero, neg_neg]⟩
  left_inv τ := Subtype.ext (by simp)
  right_inv τ := Subtype.ext (by simp)

/- English proof (translation)
Establish `h1 : Nat.card (E →+* ℂ) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} + Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}`. Rewrite using `[← Nat.card_sum]`. Conclude with `Nat.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm`. Establish `h2 : Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}` using `(Nat.card_congr (conjEquiv H)).symm`. Establish `h3 : Nat.card (E →+* ℂ) = Module.finrank ℚ E`.

Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `NumberField.Embeddings.card E ℂ`. Establish `h4 : Fintype.card (CMType H) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}`. Rewrite using `[← Nat.card_eq_fintype_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_card_CMType (H : Host E) : 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  classical
  have h1 : Nat.card (E →+* ℂ) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} +
      Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Nat.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} =
      Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} :=
    (Nat.card_congr (conjEquiv H)).symm
  have h3 : Nat.card (E →+* ℂ) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card]
    exact NumberField.Embeddings.card E ℂ
  have h4 : Fintype.card (CMType H) = Nat.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} := by
    rw [← Nat.card_eq_fintype_card]
  omega

/- English proof (translation)
Introduce `E _ _ _ H`. Use `⟨two_le_hostRd H, ?_, two_mul_card_CMType H⟩` and prove the remaining obligations. Rewrite using `[← Fintype.card_pos_iff]`. Establish `h1` using `two_mul_card_CMType H`. Establish `h2 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`.

Use linear arithmetic over natural numbers and integers.
-/
theorem host_numbers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H
  refine ⟨two_le_hostRd H, ?_, two_mul_card_CMType H⟩
  rw [← Fintype.card_pos_iff]
  have h1 := two_mul_card_CMType H
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

end GlobalTheory.CompanionTheory.Ar.Top.HostNumbers
