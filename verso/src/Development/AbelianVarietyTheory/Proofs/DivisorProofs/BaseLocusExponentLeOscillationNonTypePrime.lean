import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelHalfSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetweenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefAway

/- English proof (translation)
Rewrite using `[vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap, (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]`. Simplify using the standard rewrite rules.
-/
theorem vLa_nat_eq_zero {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ}
    (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) : vLa la (N : K) = 0 := by
  rw [vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]
  simp

/- English proof (translation)
Establish `h1 : la.valuation K (N : K) < 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 K) K) N]`. Conclude with `(la.valuation_lt_one_iff_mem _).2 hN`. Establish `h2 : la.valuation K (N : K) ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff]`.

Conclude with `h0` after adjusting the coercions. Establish `h3` using `(WithZero.log_lt_log h2 one_ne_zero).2 h1`. Rewrite `h3` using `[WithZero.log_one]`. Unfold `vLa`. Use linear arithmetic over natural numbers and integers.
-/
theorem vLa_nat_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0)
    (hN : ((N : ℕ) : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (N : K) := by
  have h1 : la.valuation K (N : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) N]
    exact (la.valuation_lt_one_iff_mem _).2 hN
  have h2 : la.valuation K (N : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast h0
  have h3 := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  unfold vLa
  omega

/- English proof (translation)
Establish `hN0 : N ≠ 0`. Introduce and unpack `rfl`. Conclude with `hN (by simp)`. Establish `h3` using `ho.2 (N : K)`. Rewrite `h3` using `[vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)]`.

Establish `hx : algebraMap S.V S.Fr (N : S.V) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hN0` after adjusting the coercions. Establish `hne` using `valV_ne_zero (V := S.V) hx`. Establish `h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1`.

Unfold `vV at h3`. Rewrite using `[← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]`. Unfold `valV at h4`. Rewrite `h4` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]`. Assume the negation of the conclusion as `hu`.

Conclude with `h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)`.
-/
theorem isUnit_nat {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h3 := ho.2 (N : K)
  rw [vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

/- English proof (translation)
Introduce `hN`. Take `⟨u, v, huv⟩` from `(Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))`. Simplify using `only [eq_intCast, Int.cast_natCast] at huv`. Conclude with `la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))`.
-/
theorem nat_not_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p N : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime p N) : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))

/- English proof (translation)
Rewrite using `[← ho.2, map_natCast]`.
-/
theorem vV_nat_eq {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) (p : ℕ) :
    vV S.V (p : S.Fr) = (e : ℤ) * vLa la (p : K) := by
  rw [← ho.2, map_natCast]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Rewrite using `[hx, nval_zero]`. Conclude with `le_top`. Establish `he : (0 : ℤ) < e` using `by exact_mod_cast ho.1`. Establish `h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ)`.

Establish `h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K)`. Rewrite using `[Int.toNat_of_nonneg, vV_nat_eq ho]`. Rewrite using `[vV_nat_eq ho]`. Check the signs of the components of the expression. Conclude with `h2` after adjusting the coercions.

Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast ho.1`. Establish `hp' : (0 : ℝ) < (vLa la (p : K) : ℝ)` using `by exact_mod_cast hp`. Rewrite `h`, the goal using `[nval_of_ne hx, EReal.coe_le_coe_iff]`. Rewrite `h` using `[h1, le_div_iff₀ (by positivity)]`. Rewrite using `[le_div_iff₀ he']`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_nval_place {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) {p : ℕ} (hp : 0 < vLa la (p : K)) (A : ℕ) (x : S.Fr)
    (h : ((A : ℝ) : EReal) ≤ nval S.V (vV S.V (p : S.Fr)).toNat x) :
    (((vLa la (p : K) * A : ℤ) : ℝ) : EReal) ≤ nval S.V e x := by
  by_cases hx : x = 0
  · rw [hx, nval_zero]; exact le_top
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ) := by
    have h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K) := by
      rw [Int.toNat_of_nonneg, vV_nat_eq ho]
      rw [vV_nat_eq ho]; positivity
    exact_mod_cast h2
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp' : (0 : ℝ) < (vLa la (p : K) : ℝ) := by exact_mod_cast hp
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  rw [h1, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he']
  push_cast
  linarith

/- English proof (translation)
Establish `h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d)`. Establish `hc` using `D.ntypes.g_cond k`. Establish `h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d)`. Rewrite using `[Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]`. Conclude with `h1`.

Conclude with `Nat.Coprime.mul_left (h 0) (h 1)`.
-/
theorem coprime_type (D : D7) : Nat.Coprime (D.host.g 0 * D.host.g 1) (D.host.QS * D.host.q * D.host.d) := by
  have h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    have hc := D.ntypes.g_cond k
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
    exact h1
  exact Nat.Coprime.mul_left (h 0) (h 1)

/- English proof (translation)
Establish `hN : 0 ≤ N` using `hρ0.trans hρ`. Combine the equalities or inequalities in the displayed calculation. Use polynomial arithmetic with `[sq_nonneg Dg]`. Use `_ ≤ _ := by gcongr`.
-/
theorem err_le (R N ρ u Dg φ c r v g₀ g₁ : ℝ) (hR : 0 ≤ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hu : 0 ≤ u) (hr : 0 < r)
    (hv : 0 < v) (hg₀ : 0 < g₀) (hg₁ : 1 ≤ g₁) (hφ : 0 ≤ φ) (hc : R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ ≤ c) :
    Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v) ≤ c * φ / v := by
  have hN : 0 ≤ N := hρ0.trans hρ
  calc Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v)
      ≤ Dg ^ 2 * (R * N ^ 3 * (r * φ)) / (g₀ * 1) / (r * v) := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ / v := by field_simp
    _ ≤ R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ * φ / v := by
      gcongr
      nlinarith [sq_nonneg Dg]
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO`. Use `letI := T.Q.H.starRing`. Establish `hqp : q.Prime` using `hq'.out`. Use `(refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_` and prove the remaining obligations. Take `⟨st, nab, hnab⟩` from `GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c`.

Take `rfl` from `GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1`. Take `⟨A, hA⟩` from `hO la`. Take `⟨P₁, hP₁, hPB⟩` from `GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA`. Take `⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩` from `GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ`. Establish `ho'` using `hov la.1 e ho`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible S'.V`. Take `⟨⟨Q, hQ⟩, -⟩` from `GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ`. Take `⟨ρ, hρ, hSB⟩` from `GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ`. Take `⟨⟨α, hα1, hα2⟩, -⟩` from `GlobalTheory.HalfGen.half_principal_and_split D T hL EX`. Take `⟨π, π', hsplit⟩` from `GlobalTheory.SplitLevel.level_halfSplit D T hL EX`.

Establish `hM : T.Q.l.M = D.host.g 0 * D.host.g 1` using `hL.pins.2.1.1`. Establish `hcop : Nat.Coprime q T.Q.l.M`. Rewrite using `[hM]`. Conclude with `Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0)) ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))`. Establish `hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V)` using `isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)`.

Establish `hr1 : 1 ≤ D.R.r`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.

Establish `hn1 : 1 ≤ n` using `by omega`. Establish `hρN : ρ ≤ 2 * D.R.f * D.R.m`. Use `hρ.trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]`. Conclude with `Nat.mul_le_mul_left _ (Nat.sub_le _ _)`.

Establish `hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m` using `by exact_mod_cast hρN`. Establish `hg0 : 2 ≤ D.host.g 0` using `(D.host.g_prime 0).two_le`. Establish `hg1 : 2 ≤ D.host.g 1` using `(D.host.g_prime 1).two_le`. Establish `hle : D.host.g 0 ≤ T.Q.l.M` using `hM ▸ Nat.le_mul_of_pos_right _ (by omega)`. Establish `hg0' : (2 : ℝ) ≤ D.host.g 0` using `by exact_mod_cast hg0`.

Establish `hg1' : (2 : ℝ) ≤ D.host.g 1` using `by exact_mod_cast hg1`. Establish `hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ)` using `by exact_mod_cast hle`. Establish `hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ)`. Use `lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')` and prove the remaining obligations. Use `gcongr`.

Establish `hε : 0 < vLa la.1 (q : T.Q.c.F)` using `vLa_nat_pos la.1 hqp.ne_zero la.2`. Establish `hv0 : 0 < vV S.V (q : S.Fr)`. Rewrite using `[vV_nat_eq ho]`. Conclude with `mul_pos (by exact_mod_cast ho.1) hε`. Take `⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v` from `⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩`.

Establish `hvpos : 0 < v` using `by omega`. Establish `hv' : (vV S'.V (q : S'.Fr)).toNat = r * v`. Rewrite using `[hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]`. Establish `hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F)`. Rewrite using `[← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]`.

Establish `hr0' : (0 : ℝ) < r` using `by exact_mod_cast hr0`. Establish `hvpos' : (0 : ℝ) < v` using `by exact_mod_cast hvpos`. Establish `hup` using `GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁`. Establish `hloc` using `(hPB S' io' _ ho' y' hy' C T.Q.l.M).2`. Rewrite `hloc` using `[hv']`.

Establish `hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤ cst * φ / v`. Rewrite using `[hM, Nat.cast_mul, Nat.cast_mul]`. Use `err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith) hφ.nonneg (hJ 0).2.2` and prove the remaining obligations. Unfold `rr0`. Check the signs of the components of the expression.

Check the signs of the components of the expression. Establish `hinf` using `hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))`. Take `⟨m, hm, hmlow, -⟩` from `GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit (coprime_type D) a n`. Establish `hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤ ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f), nval S'.V (r * v) (evI y' f)`. Use `le_iInf₂ fun f ⟨x, hx⟩ => ?_` and prove the remaining obligations.

Establish `hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n` using `⟨x, P₁, hP₁, hx⟩`. Establish `hcusp` using `(GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2 a n hD hLP f hf`. Establish `hlow` using `GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx`. Take `⟨s, hs0, hsv, g, hg, hgs⟩` from `GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n) ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by`. Introduce and unpack `_ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩`.

Conclude with `le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))`. Establish `h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f)`. Use `(iInf₂_le g hg).trans (le_of_eq ?_)` and prove the remaining obligations. Use `show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _`. Rewrite using `[hv, Int.toNat_natCast, hgs, evI_smul]`.

Establish `h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal)`. Rewrite using `[nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]`. Use `congr 1`. Establish `h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ)` using `by exact_mod_cast hrv`. Establish `h4 : ((r * v : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'`.

Rewrite using `[div_eq_iff h4, h3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[← hsc nab hnab a n v s f hf, nval_mul, h2]`. Use `(add_le_add h1 le_rfl).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]`. Establish `hfin` using `hdep.trans hinf`. Rewrite using `[hv, Int.cast_natCast]`. Rewrite `hfin` using `[← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add, ← EReal.coe_sub]`. Rewrite using `[← EReal.coe_add]`.

Conclude with `hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))`.
-/
theorem refExp_le_of_oscLe : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  intro D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO
  letI := T.Q.H.starRing
  have hqp : q.Prime := hq'.out
  refine (refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1
  obtain ⟨A, hA⟩ := hO la
  obtain ⟨P₁, hP₁, hPB⟩ := GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA
  obtain ⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  have ho' := hov la.1 e ho
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T hL EX
  obtain ⟨π, π', hsplit⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hL EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  have hcop : Nat.Coprime q T.Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0))
      ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V) := isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ n := by omega
  have hρN : ρ ≤ 2 * D.R.f * D.R.m := by
    refine hρ.trans ?_
    rw [GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hρN
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ T.Q.l.M := hM ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by exact_mod_cast hle
  have hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ) := by
    refine lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')
    gcongr

  have hε : 0 < vLa la.1 (q : T.Q.c.F) := vLa_nat_pos la.1 hqp.ne_zero la.2
  have hv0 : 0 < vV S.V (q : S.Fr) := by
    rw [vV_nat_eq ho]
    exact mul_pos (by exact_mod_cast ho.1) hε
  obtain ⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v := ⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩
  have hvpos : 0 < v := by omega
  have hv' : (vV S'.V (q : S'.Fr)).toNat = r * v := by
    rw [hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]
  have hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F) := by
    rw [← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos

  have hup := GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB
    α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁
  have hloc := (hPB S' io' _ ho' y' hy' C T.Q.l.M).2
  rw [hv'] at hloc
  have hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤
      cst * φ / v := by
    rw [hM, Nat.cast_mul, Nat.cast_mul]
    refine err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith)
      hφ.nonneg (hJ 0).2.2
    · unfold rr0; positivity
    · positivity
  have hinf := hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))

  obtain ⟨m, hm, hmlow, -⟩ := GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit
    (coprime_type D) a n
  have hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤
      ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f),
        nval S'.V (r * v) (evI y' f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n := ⟨x, P₁, hP₁, hx⟩
    have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2
      a n hD hLP f hf
    have hlow := GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp
      (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx
    obtain ⟨s, hs0, hsv, g, hg, hgs⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n)
      ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by
        rintro _ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩
        exact le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))
    have h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f) := by
      refine (iInf₂_le g hg).trans (le_of_eq ?_)
      show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _
      rw [hv, Int.toNat_natCast, hgs, evI_smul]
    have h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]
      congr 1
      have h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ) := by exact_mod_cast hrv
      have h4 : ((r * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'
      rw [div_eq_iff h4, h3]
      push_cast
      ring
    rw [← hsc nab hnab a n v s f hf, nval_mul, h2] at h1
    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
    rw [add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  have hfin := hdep.trans hinf
  rw [hv, Int.cast_natCast]
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    ← EReal.coe_sub] at hfin
  rw [← EReal.coe_add]
  exact hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.RefAway

end
