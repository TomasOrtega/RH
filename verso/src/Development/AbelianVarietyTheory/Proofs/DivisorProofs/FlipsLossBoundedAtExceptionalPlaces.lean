import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralLocalGridTensorOfLevelChar
import Development.AutomorphicArithmetic.DivisorFrames.AbsHcExponentLeAndAbsCenterLeOfSizeRows
import Development.AutomorphicArithmetic.LocalEmbeddings.FlipVal
import Development.AutomorphicArithmetic.LocalEmbeddings.FlipInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

section SlopeTestRemainingChoices

open ValuativeRel UpperTheory.FlipInt UpperTheory.FlipVal

/- English proof (translation)
Use `haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Establish `e` using `ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))`. Use `set q := Ideal.absNorm w.asIdeal`. Establish `hq0 : q ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot`. Establish `hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ)`.

Establish `hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1` using `by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal`. Establish `h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E)`. Rewrite using `[← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)`. Rewrite using `[h2]`.

Use `(w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem` as an intermediate fact. Simplify using `using this`. Establish `hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ)` using `Formalism.L2.Host.unif_spec w`. Establish `hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1`. Use `(e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)` as an intermediate fact.

Rewrite `this` using `[map_one]`. Then use the resulting hypothesis. Establish `hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1`. Use `le_trans ?_ hx'` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]`. Use `gcongr`.

Establish `hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1` using `(e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)`. Establish `h1 : ψ ((q ^ n) • x) = 1`. Rewrite using `[nsmul_eq_mul]`. Conclude with `(hc 1).2 (by simp) _ hNx2`. Use `IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero n hq0)) ?_` and prove the remaining obligations.

Rewrite using `[← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]`. Conclude with `isIntegral_one`.
-/
private theorem psi_int {D : D7} {w : Pl D.host.E} {ψ : AddChar (Kw w) Circle} (hc : HasConductor ψ 1) (n : ℕ) (x : Kw w)
    (hx : valuation (Kw w) ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1) : IsIntegral ℤ (ψ x : ℂ) := by
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
  set q := Ideal.absNorm w.asIdeal
  have hq0 : q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hq : Valued.v ((q : ℕ) : Kw w) ≤ WithZero.exp (-1 : ℤ) := by
    have hmem : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem w.asIdeal
    have h2 : Valued.v ((q : ℕ) : Kw w) = w.intValuation ((q:ℕ) : 𝓞 D.host.E) := by
      rw [← map_natCast (algebraMap (𝓞 D.host.E) (Kw w))]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.E) w _).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _)
    rw [h2]
    have := (w.intValuation_le_pow_iff_mem ((q:ℕ) : 𝓞 D.host.E) 1).2 hmem
    simpa using this
  have hu : Valued.v ((unifAt w : (Kw w)ˣ) : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  have hx' : Valued.v ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) ≤ 1 := by
    have := (e ((((unifAt w) ^ n : (Kw w)ˣ) : Kw w) * x) 1).1 (by rw [map_one]; exact hx)
    rwa [map_one] at this
  have hNx : Valued.v (((q ^ n : ℕ) : Kw w) * x) ≤ 1 := by
    refine le_trans ?_ hx'
    rw [map_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Nat.cast_pow, map_pow, hu]
    gcongr
  have hNx2 : valuation (Kw w) (((q ^ n : ℕ) : Kw w) * x) ≤ valuation (Kw w) 1 :=
    (e (((q ^ n : ℕ) : Kw w) * x) 1).2 (by rw [map_one]; exact hNx)
  have h1 : ψ ((q ^ n) • x) = 1 := by
    rw [nsmul_eq_mul]
    exact (hc 1).2 (by simp) _ hNx2
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pow_ne_zero n hq0)) ?_
  rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, h1, Circle.coe_one]
  exact isIntegral_one

/- English proof (translation)
Establish `h1 : Function.Injective (Formalism.L2.Host.embTau D)` using `GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_injective D`. Establish `h2 : ∀ τ τ', ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D τ) ≠ Formalism.L2.Host.embTau D τ'` using `fun τ τ' h => GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_ne_bar D τ τ' ((RingHom.ext fun _ => rfl).trans h)`. Use `h1.sumElim (fun a b h => h1 (star_injective h)) fun a b h => h2 b a h.symm` and prove the remaining obligations.
-/
private theorem emb_inj (D : D7) : Function.Injective
    (Sum.elim (Formalism.L2.Host.embTau D) fun i => ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D i)) := by
  have h1 : Function.Injective (Formalism.L2.Host.embTau D) := GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_injective D
  have h2 : ∀ τ τ', ComplexEmbedding.conjugate (Formalism.L2.Host.embTau D τ) ≠ Formalism.L2.Host.embTau D τ' := fun τ τ' h =>
    GlobalTheory.Survey.EmbeddingValuationsAnti.embTau_ne_bar D τ τ' ((RingHom.ext fun _ => rfl).trans h)
  refine h1.sumElim (fun a b h => h1 (star_injective h)) fun a b h => h2 b a h.symm

/- English proof (translation)
Introduce `x hx h'` and use `h x hx (h'.trans (WithZero.exp_le_exp.2 (by norm_num)))`.
-/
private theorem lev_two {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {v : HeightOneSpectrum (𝓞 E)}
    (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx h' => h x hx (h'.trans (WithZero.exp_le_exp.2 (by norm_num)))

/- English proof (translation)
Take `⟨b1, b2⟩` from `UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows D large₂ hS hH`. Establish `h12` using `(GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS).2.2.2.2.2.2.2`. Establish `e1 : (((locGrid G t w).nu i j (unifAt w) : ℂˣ) : ℂ) = ((L.C.mu0 ⟨j, hj⟩).val w : ℂ) * ((L.xiH t).val w : ℂ) * (((G.ch.chiH (D.R.m - i)).val w : ℂ))⁻¹`. Simplify using `only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]`.

Both sides reduce to the same expression. Establish `hμ` using `L.C.isMu0 ⟨j, hj⟩`. Take `⟨n, hn, hinf⟩` from `GlobalTheory.Chain.StepVac.hasInfQ_tau hμ.inf`. Establish `hg0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0`. Conclude with `mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero` after adjusting the coercions.

Take `⟨m1, m2⟩` from `val_int (L.C.mu0 ⟨j, hj⟩) (Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)) (fun v hv => hμ.unr v fun k hk => hv (by`. Rewrite using `[Formalism.L2.DIV.mem_primesOf, and_iff_right hg0, Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem]`. Use `fin_cases k`. Use `exacts [Or.inl hk, Or.inr hk])) (fun v => lev_two (hμ.tame v)) (Formalism.L2.Host.embTau D) (emb_inj D) n hinf`. Use the proof step `⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by`.

Establish `h1` using `hn τ`. Simplify using `only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1`. Establish `h2 : (n τ : ℝ) = 2 * -(((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ)` using `by exact_mod_cast h1`. Establish `h3` using `b1 τ ⟨j, hj⟩`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs, h2, abs_mul, abs_neg, abs_two]`.

Use the proof step `linarith)) w`. Establish `hi1 : 1 ≤ D.R.m - i` using `by omega`. Establish `hi2 : D.R.m - i ≤ D.R.m` using `by omega`. Take `⟨c1, c2⟩` from `val_int (G.ch.chiH (D.R.m - i)) (G.pl.S0.biUnion (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F)) (fun v hv => G.ch.unr _ hi1 hi2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, h, by simp [Formalism.L2.Host.aboveF]⟩)) (fun v => by`. Distinguish the cases in `h : v.under (𝓞 D.host.F) ∈ G.pl.S0`.

Break down `G.pl.mem_S0_of_sum_eq.1 h with h | h` into its components or cases. Conclude with `lev_two (G.ch.lev0 _ hi1 hi2 v h).1`. Conclude with `(G.ch.lev1 _ hi1 hi2 v h).1`. Conclude with `fun x hx _ => G.ch.unr _ hi1 hi2 v h x hx) (Formalism.L2.Host.embTau D) (emb_inj D) _ (G.ch.inf _ hi1 hi2)`. Use the proof step `⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by`.

Establish `h3` using `b2 τ _ hi1 hi2`. Rewrite using `[Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul, Int.cast_ofNat, abs_two, hc]`. Use the proof step `linarith)) w`. Take `⟨N, hN, hord⟩` from `hL.xi_fin t`. Establish `hx : ((L.xiH t).val w : ℂ) ^ N = 1`.

Establish `h1 : ((L.xiH t) ^ N).val w = 1` using `by rw [show (L.xiH t) ^ N = 1 from hord]; rfl`. Establish `h2 : ((L.xiH t) ^ N).val w = (L.xiH t).val w ^ N` using `rfl`. Rewrite using `[← Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one]`. Establish `x1 : IsIntegral ℤ ((L.xiH t).val w : ℂ)` using `IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one)`. Establish `x2 : IsIntegral ℤ ((L.xiH t).val w : ℂ)⁻¹` using `IsIntegral.of_pow hN (by rw [inv_pow, hx, inv_one]; exact isIntegral_one)`.

Rewrite using `[map_inv, Units.val_inv_eq_inv_val, e1, two_mul]`. Use `⟨Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m1) (Lo_zero x1)) (mem_Lo.2 c2), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv, mul_inv, inv_inv]`. Conclude with `Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m2) (Lo_zero x2)) (mem_Lo.2 c1)`.
-/
private theorem nu_int {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) (t : T) (w : Pl D.host.E)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) :
    ((locGrid G t w).nu i j (unifAt w) : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) ∧
      ((locGrid G t w).nu i j (unifAt w)⁻¹ : ℂ) ∈ Lo (Ideal.absNorm w.asIdeal) (2 * ⌊8 * large₂.sc.b⌋₊) := by
  classical
  obtain ⟨b1, b2⟩ := UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows D large₂ hS hH
  have h12 := (GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS).2.2.2.2.2.2.2
  have e1 : (((locGrid G t w).nu i j (unifAt w) : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).val w : ℂ) * ((L.xiH t).val w : ℂ) * (((G.ch.chiH (D.R.m - i)).val w : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hμ := L.C.isMu0 ⟨j, hj⟩
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.Chain.StepVac.hasInfQ_tau hμ.inf
  have hg0 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨m1, m2⟩ := val_int (L.C.mu0 ⟨j, hj⟩) (Formalism.L2.DIV.primesOf ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E))
    (fun v hv => hμ.unr v fun k hk => hv (by
      rw [Formalism.L2.DIV.mem_primesOf, and_iff_right hg0, Nat.cast_mul, v.isPrime.mul_mem_iff_mem_or_mem]
      fin_cases k
      exacts [Or.inl hk, Or.inr hk])) (fun v => lev_two (hμ.tame v)) (Formalism.L2.Host.embTau D) (emb_inj D) n hinf
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h1 := hn τ
      simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
      have h2 : (n τ : ℝ) = 2 * -(((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by exact_mod_cast h1
      have h3 := b1 τ ⟨j, hj⟩
      rw [Nat.cast_natAbs, Int.cast_abs, h2, abs_mul, abs_neg, abs_two]
      linarith)) w
  have hi1 : 1 ≤ D.R.m - i := by omega
  have hi2 : D.R.m - i ≤ D.R.m := by omega
  obtain ⟨c1, c2⟩ := val_int (G.ch.chiH (D.R.m - i)) (G.pl.S0.biUnion (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F))
    (fun v hv => G.ch.unr _ hi1 hi2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, h, by simp [Formalism.L2.Host.aboveF]⟩))
    (fun v => by
      by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
        · exact lev_two (G.ch.lev0 _ hi1 hi2 v h).1
        · exact (G.ch.lev1 _ hi1 hi2 v h).1
      · exact fun x hx _ => G.ch.unr _ hi1 hi2 v h x hx) (Formalism.L2.Host.embTau D) (emb_inj D) _ (G.ch.inf _ hi1 hi2)
    ⌊8 * large₂.sc.b⌋₊ (fun τ => Nat.le_floor (by
      have h3 := b2 τ _ hi1 hi2
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul, Int.cast_ofNat, abs_two, hc]
      linarith)) w
  obtain ⟨N, hN, hord⟩ := hL.xi_fin t
  have hx : ((L.xiH t).val w : ℂ) ^ N = 1 := by
    have h1 : ((L.xiH t) ^ N).val w = 1 := by rw [show (L.xiH t) ^ N = 1 from hord]; rfl
    have h2 : ((L.xiH t) ^ N).val w = (L.xiH t).val w ^ N := rfl
    rw [← Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one]
  have x1 : IsIntegral ℤ ((L.xiH t).val w : ℂ) := IsIntegral.of_pow hN (by rw [hx]; exact isIntegral_one)
  have x2 : IsIntegral ℤ ((L.xiH t).val w : ℂ)⁻¹ := IsIntegral.of_pow hN (by rw [inv_pow, hx, inv_one]; exact isIntegral_one)
  rw [map_inv, Units.val_inv_eq_inv_val, e1, two_mul]
  refine ⟨Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m1) (Lo_zero x1)) (mem_Lo.2 c2), ?_⟩
  rw [mul_inv, mul_inv, inv_inv]
  exact Lo_mul (Lo_mul (b := 0) (mem_Lo.2 m2) (Lo_zero x2)) (mem_Lo.2 c1)

end SlopeTestRemainingChoices

/- English proof (translation)
Use `⟨0, fun CF _ => ⟨56, fun ε => ⟨0, ?_⟩⟩⟩` and prove the remaining obligations. Introduce `D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc hF t Φ w hw la hla z`. Establish `hL : R.toLevCh.Is A.μ0` using `hS.core.lev`. Establish `hde` using `GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS`. Establish `hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `hch.guard t`.

Establish `hg` using `(Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw`. Establish `hadm` using `GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `h00` using `hg.square 0 hm 0 hm`. Establish `hq : resCard (Kw w) = Ideal.absNorm w.asIdeal` using `GlobalTheory.LFun.SatBoundGL.resCard_completion w`.

Establish `hq0 : resCard (Kw w) ≠ 0` using `by rw [hq]; exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot`. Establish `hgap : ch.sc.cGap = 1` using `by rw [show ch.sc = _ from hsc]`. Establish `hfl : ∀ x ∈ flipOrder D.R.m, x.1 < D.R.m ∧ x.2 < D.R.m ∧ CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2)`. Introduce `x hx`. Simplify using `only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx`.

Take `⟨i, hi, j, hj, rfl⟩` from `hx`. Establish `hs` using `hg.square i hi j hj`. Establish `e` using `(locGrid ch.G t w).alpha_div_beta i j`. Conclude with `⟨hi, hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram⟩`. Set `K : Subfield ℂ` to `D.what₂.embLL.fieldRange`.

Establish `hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K` using `fun y hy => RingHom.mem_fieldRange.2 hy`. Establish `hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K` using `fun j x => hK _ (hF.chars.mu0 j w x)`. Establish `hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K` using `fun x => hK _ (hF.chars.xi t w x)`. Establish `hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K` using `fun i a b x => hK _ (hF.chars.chi i a b w x)`. Establish `habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K` using `GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))`.

Establish `hψ` using `GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond`. Take `⟨y, hy⟩ : ∃ y, D.what₂.embLL y = Tflip ch.W ch.S.B t Φ w z` from `RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m) (givenStage t w ch.S.B Φ) (fun x hx => ⟨(hfl x hx).2.2.1, (hfl x hx).2.2.2, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi (hfl x hx).1 (hfl x hx).2.1⟩) (canFli …`. Establish `key : Tflip ch.W ch.S.B t Φ w z ∈ UpperTheory.FlipInt.Lo (resCard (Kw w)) (0 + (flipOrder D.R.m).length * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)))`. Use `UpperTheory.FlipInt.flips_mem h00.unif h00.cond h00.one_le hq0 (psi_int h00.cond _) (flipOrder D.R.m) (givenStage t w ch.S.B Φ) 0 (fun x hx => ?_) (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm (fun z => UpperTheory.FlipInt.Lo_zero (UpperTheory.isIntegra …` and prove the remaining obligations. Take `⟨hi, hj, h1, h2⟩` from `hfl x hx`.

Establish `h3` using `nu_int ch.G hL large₂ hS.size hS.host hgap t w hi hj`. Rewrite `h3` using `[← hq]`. Use `⟨h1, h2, h3.1, h3.2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.R.r + (x.2 + 1) * D.R.t + (x.1 + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)`. Establish `a1 : (x.2 + 1) * D.R.t ≤ D.R.m * D.R.t` using `Nat.mul_le_mul_right _ hj`.

Establish `a2 : (x.1 + 1) * sLen D ≤ D.R.m * sLen D` using `Nat.mul_le_mul_right _ hi`. Establish `a3 : D.R.r ≤ D.R.k + D.R.m` using `by unfold Ranks.r; omega`. Rewrite using `[mul_add, mul_add]`. Use linear arithmetic over natural numbers and integers. Rewrite `key` using `[zero_add, (canFlip_flipOrder _).2.1, UpperTheory.FlipInt.mem_Lo, ← hy, ← map_natCast D.what₂.embLL, ← map_pow, ← map_mul]`.

Use `replace key := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 key`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy0 : y = 0`. Conclude with `Or.inl hy0`. Use `Or.inr ?_` and prove the remaining obligations.

Establish `h1` using `UpperTheory.FlipVal.vw_ge la hy0 hq0 _ key`. Establish `h2 : -(((D.R.m ^ 2 * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)) : ℕ) : ℝ) * (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)) ≤ (vw la y : ℝ)` using `by exact_mod_cast h1`. Use `le_trans (neg_le_neg ?_) h2` and prove the remaining obligations. Distinguish the cases in `hW : w ∈ ch.G.pl.W0`. Establish `hd : depthAt ch.G w = cosExp ch.G w`.

Rewrite using `[depthAt, max_eq_left]`. Rewrite using `[cosExp, if_pos hW]`. Conclude with `ch.G.pl.depth_pos _ _`. Take `⟨s1, -, s2, -, -, -, -, s3⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size`. Establish `s2' : (1 : ℝ) ≤ bigN D` using `by exact_mod_cast s2`.

Establish `s4 : (⌊8 * large₂.sc.b⌋₊ : ℝ) ≤ 8 * large₂.sc.b` using `Nat.floor_le (by linarith)`. Establish `s5 : (0 : ℝ) ≤ (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)`. Conclude with `UpperTheory.FlipVal.vw_nat_nonneg la _` after adjusting the coercions. Use `mul_le_mul_of_nonneg_right ?_ s5` and prove the remaining obligations. Rewrite using `[hd]`.

Use `push_cast`. Establish `s6 : 3 * (2 * (⌊8 * large₂.sc.b⌋₊ : ℝ)) + 8 * bigN D ≤ 56 * (bigN D * large₂.sc.b)` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) = 0`. Rewrite using `[hq]`.

Conclude with `UpperTheory.FlipVal.vw_absNorm la w (hla.resolve_left hW)`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.T.flips_loss_bounded_at_exceptional_places : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ c₁ : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK →
      ∀ (t : T) (Φ : ch.G.Datum) (P : Pl D.host.E), P ∈ locPl ch.G t → ∀ w : PlL D,
        (P ∈ ch.G.pl.W0 ∨ ((Formalism.EigenvalueLevelCeiling.plc P : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal) →
        ∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) (c₁ * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * large₂.sc.b * (cosExp ch.G P : ℝ) *
          (vw w ((resCard (Kw P) : ℕ) : D.what₂.LL) : ℝ)) := by
  refine ⟨0, fun CF _ => ⟨56, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc hF t Φ w hw la hla z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hq : resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hq0 : resCard (Kw w) ≠ 0 := by rw [hq]; exact Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot
  have hgap : ch.sc.cGap = 1 := by rw [show ch.sc = _ from hsc]
  have hfl : ∀ x ∈ flipOrder D.R.m, x.1 < D.R.m ∧ x.2 < D.R.m ∧
      CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧ ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    exact ⟨hi, hj, by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram⟩

  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  obtain ⟨y, hy⟩ : ∃ y, D.what₂.embLL y = Tflip ch.W ch.S.B t Φ w z :=
    RingHom.mem_fieldRange.1 (GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ)
      (fun x hx => ⟨(hfl x hx).2.2.1, (hfl x hx).2.2.2, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi (hfl x hx).1 (hfl x hx).2.1⟩)
      (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
      (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z)

  have key : Tflip ch.W ch.S.B t Φ w z ∈ UpperTheory.FlipInt.Lo (resCard (Kw w)) (0 + (flipOrder D.R.m).length *
      (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D))) := by
    refine UpperTheory.FlipInt.flips_mem h00.unif h00.cond h00.one_le hq0 (psi_int h00.cond _) (flipOrder D.R.m)
      (givenStage t w ch.S.B Φ) 0 (fun x hx => ?_) (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm
      (fun z => UpperTheory.FlipInt.Lo_zero (UpperTheory.isIntegral_localGrid_tensor_of_levelChar hL ch.S.B t Φ w z)) z
    obtain ⟨hi, hj, h1, h2⟩ := hfl x hx
    have h3 := nu_int ch.G hL large₂ hS.size hS.host hgap t w hi hj
    rw [← hq] at h3
    refine ⟨h1, h2, h3.1, h3.2, ?_⟩
    change D.R.r + (x.2 + 1) * D.R.t + (x.1 + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have a1 : (x.2 + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have a2 : (x.1 + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have a3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    rw [mul_add, mul_add]; omega
  rw [zero_add, (canFlip_flipOrder _).2.1, UpperTheory.FlipInt.mem_Lo, ← hy, ← map_natCast D.what₂.embLL, ← map_pow, ← map_mul] at key
  replace key := (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 key
  refine ⟨y, hy, ?_⟩
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  refine Or.inr ?_
  have h1 := UpperTheory.FlipVal.vw_ge la hy0 hq0 _ key
  have h2 : -(((D.R.m ^ 2 * (depthAt ch.G w * bigN D * (3 * (2 * ⌊8 * large₂.sc.b⌋₊) + 8 * bigN D)) : ℕ) : ℝ) *
      (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ)) ≤ (vw la y : ℝ) := by exact_mod_cast h1
  refine le_trans (neg_le_neg ?_) h2
  by_cases hW : w ∈ ch.G.pl.W0
  · have hd : depthAt ch.G w = cosExp ch.G w := by
      rw [depthAt, max_eq_left]
      rw [cosExp, if_pos hW]
      exact ch.G.pl.depth_pos _ _
    obtain ⟨s1, -, s2, -, -, -, -, s3⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
    have s2' : (1 : ℝ) ≤ bigN D := by exact_mod_cast s2
    have s4 : (⌊8 * large₂.sc.b⌋₊ : ℝ) ≤ 8 * large₂.sc.b := Nat.floor_le (by linarith)
    have s5 : (0 : ℝ) ≤ (vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) : ℝ) := by
      exact_mod_cast UpperTheory.FlipVal.vw_nat_nonneg la _
    refine mul_le_mul_of_nonneg_right ?_ s5
    rw [hd]
    push_cast
    have s6 : 3 * (2 * (⌊8 * large₂.sc.b⌋₊ : ℝ)) + 8 * bigN D ≤ 56 * (bigN D * large₂.sc.b) := by nlinarith
    calc _ ≤ (D.R.m : ℝ) ^ 2 * ((cosExp ch.G w : ℝ) * bigN D * (56 * (bigN D * large₂.sc.b))) := by gcongr
      _ = _ := by ring
  · have h0 : vw la ((resCard (Kw w) : ℕ) : D.what₂.LL) = 0 := by
      rw [hq]; exact UpperTheory.FlipVal.vw_absNorm la w (hla.resolve_left hW)
    rw [h0]; simp
